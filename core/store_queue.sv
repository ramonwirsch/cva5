/*
 * Copyright © 2020 Eric Matthews,  Lesley Shannon
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * Initial code developed under the supervision of Dr. Lesley Shannon,
 * Reconfigurable Computing Lab, Simon Fraser University.
 *
 * Author(s):
 *             Eric Matthews <ematthew@sfu.ca>
 */

module store_queue

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter rf_params_t RF_CONFIG = get_derived_rf_params(CONFIG)
    )
    ( 
        input logic clk,
        input logic rst,

        input logic lq_push,
        input logic lq_pop,
        store_queue_interface.queue sq,

        //Address hash (shared by loads and stores)
        input addr_hash_t addr_hash,
        //hash check on adding a load to the queue
        output logic [CONFIG.SQ_DEPTH-1:0] potential_store_conflicts,
        //Load issue collision check
        input logic [CONFIG.SQ_DEPTH-1:0] prev_store_conflicts,
        output logic store_conflict,

        //Writeback snooping
        input wb_packet_t wb_snoop [RF_CONFIG.TOTAL_WB_GROUP_COUNT-1], // port0 ignored, writes immediately

        // interface to id_unit for committing of memory ops and tracking
        memory_commit_interface.ls mem_commit
    );

    localparam LOG2_SQ_DEPTH = $clog2(CONFIG.SQ_DEPTH);
    localparam SNOOP_PORTS = RF_CONFIG.TOTAL_WB_GROUP_COUNT-1;
    localparam SNOOP_PORTS_FLOAT_START = RF_CONFIG.FP_WB_PORT;
    typedef logic [LOG2_MAX_IDS:0] load_check_count_t;

    typedef struct packed {
        id_t idNeeded;
        logic isFloat;
    } forward_selector_t;

    typedef struct packed {
        logic [31:0] addr;
        logic [3:0] be;
        logic [2:0] fn3;
        mem_subunit_t subunit_id;
        logic is_amo_sc;
        logic is_amo_rmw;
        logic [4:0] amo_op;
        logic has_paired_load;
    } sq_internal_t;


    wb_packet_t wb_snoop_r [SNOOP_PORTS];

    //Register-based memory blocks
    logic [CONFIG.SQ_DEPTH-1:0] valid;
    logic [CONFIG.SQ_DEPTH-1:0] valid_next;
    logic [CONFIG.SQ_DEPTH-1:0] strictly_ordered;
    addr_hash_t [CONFIG.SQ_DEPTH-1:0] hashes;
    logic [CONFIG.SQ_DEPTH-1:0] released;
    forward_selector_t [CONFIG.SQ_DEPTH-1:0] forward_selector;
    logic [CONFIG.SQ_DEPTH-1:0] snoop_outstanding;
    load_check_count_t [CONFIG.SQ_DEPTH-1:0] load_check_count;
    logic [31:0] data_to_store [CONFIG.SQ_DEPTH];
    logic [31:0] sq_in_data_processed;

    //LUTRAM-based memory blocks
    sq_internal_t sq_entry_in;
    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(sq_internal_t)-1:0] sq_entry [CONFIG.SQ_DEPTH];
    (* ramstyle = "MLAB, no_rw_check" *) id_t [CONFIG.SQ_DEPTH-1:0] ids;
    (* ramstyle = "MLAB, no_rw_check" *) logic [LOG2_SQ_DEPTH-1:0] sq_ids [MAX_IDS];

    load_check_count_t [CONFIG.SQ_DEPTH-1:0] load_check_count_next;

    logic [LOG2_SQ_DEPTH-1:0] sq_index;
    logic [LOG2_SQ_DEPTH-1:0] sq_index_next;
    logic [LOG2_SQ_DEPTH-1:0] sq_oldest;

    logic [CONFIG.SQ_DEPTH-1:0] new_request_one_hot;
    logic [CONFIG.SQ_DEPTH-1:0] issued_one_hot;


    logic [CONFIG.SQ_DEPTH-1:0] wb_id_match;

    ////////////////////////////////////////////////////
    //Implementation     
    assign sq_index_next = sq_index +LOG2_SQ_DEPTH'(sq.push);
    always_ff @ (posedge clk) begin
        if (rst)
            sq_index <= 0;
        else
            sq_index <= sq_index_next;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            sq_oldest <= 0;
        else
            sq_oldest <= sq_oldest +LOG2_SQ_DEPTH'(sq.pop);
    end

    assign new_request_one_hot = CONFIG.SQ_DEPTH'(sq.push) << sq_index;
    assign issued_one_hot = CONFIG.SQ_DEPTH'(sq.pop) << sq_oldest;

    assign valid_next = (valid | new_request_one_hot) & ~issued_one_hot;
    always_ff @ (posedge clk) begin
        if (rst)
            valid <= '0;
        else
            valid <= valid_next;
    end

    assign sq.empty = ~|valid;

    always_ff @ (posedge clk) begin
        if (rst)
            sq.full <= 0;
        else
            sq.full <= valid_next[sq_index_next] | (|load_check_count_next[sq_index_next]);
    end

    //SQ attributes and issue data
    assign sq_entry_in = '{ // TODO: if we need 1 cycle for converting FP->IEEE, then override FP-stores as forwarded-stores and convert there (already reg (wb_packet_r) -> reg(forwarded_data))
        addr : sq.data_in.addr,
        be : (sq.data_in.store)? sq.data_in.be : 4'b0,
        fn3 : sq.data_in.fn3,
//        data : sq_in_data_processed,
        subunit_id : sq.data_in.subunit_id,
        is_amo_sc : sq.data_in.amo.is_sc,
        is_amo_rmw : sq.data_in.amo.is_rmw,
        amo_op : sq.data_in.amo.op,
        has_paired_load : sq.data_in.load
    };
    always_ff @ (posedge clk) begin
        if (sq.push)
            sq_entry[sq_index] <= sq_entry_in;
    end

    always_ff @(posedge clk) begin
        if (sq.push)
            strictly_ordered[sq_index] <= sq.data_in.strictly_ordered;
    end

    //Hash mem
    always_ff @ (posedge clk) begin
        if (sq.push)
            hashes[sq_index] <= addr_hash;
    end

    //Keep count of the number of pending loads that might need a store result
    //Mask out any store completing on this cycle
    logic [CONFIG.SQ_DEPTH-1:0] strictly_ordered_match;
    logic [CONFIG.SQ_DEPTH-1:0] addr_hash_match;
    logic [CONFIG.SQ_DEPTH-1:0] new_load_waiting;
    logic [CONFIG.SQ_DEPTH-1:0] waiting_load_completed;

    always_comb begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            strictly_ordered_match[i] = sq.data_in.strictly_ordered && strictly_ordered[i]; // new load being queued is marked as strictly ordered towards stores already queued
            addr_hash_match[i] = addr_hash == hashes[i]; // new load being queued matches addr of stores already queued
            potential_store_conflicts[i] = (valid[i] && ~issued_one_hot[i]) && (strictly_ordered_match[i] || addr_hash_match[i]); // remember which stores came before that load and store that with that queued load
            new_load_waiting[i] = potential_store_conflicts[i] & lq_push;
            waiting_load_completed[i] = prev_store_conflicts[i] & lq_pop;

            load_check_count_next[i] =
                load_check_count[i]
                + LOG2_MAX_IDS'(new_load_waiting[i])
                - LOG2_MAX_IDS'(waiting_load_completed[i]);
        end
    end
    always_ff @ (posedge clk) begin
        if (rst)
            load_check_count <= '0;
        else
            load_check_count <= load_check_count_next;
    end

    //If a potential blocking store has not been issued yet, the load is blocked until the store(s) complete
    assign store_conflict = |(prev_store_conflicts & valid);

    ////////////////////////////////////////////////////
    //ID Handling

    //sq_id to global_id mem
    always_ff @ (posedge clk) begin
        if (sq.push)
            ids[sq_index] <= sq.data_in.id;
    end
    // global_id to sq_id mem
    always_ff @ (posedge clk) begin
        if (rst)
            for (int i=0; i < MAX_IDS; i++)
                sq_ids[i] <= '0;
        else if (sq.push)
            sq_ids[sq.data_in.id] <= sq_index;
    end
    //waiting on ID mem
    always_ff @ (posedge clk) begin
        if (sq.push) begin
            forward_selector[sq_index] <= '{ idNeeded: sq.data_in.id_needed, isFloat: CONFIG.INCLUDE_FPU_SINGLE && sq.data_in.is_float };
        end
    end

    ////////////////////////////////////////////////////
    //Release Handling
    logic [CONFIG.SQ_DEPTH-1:0] newly_released;
    logic [LOG2_SQ_DEPTH-1:0] store_released_index [RETIRE_PORTS];
    logic store_released [RETIRE_PORTS];
    always_comb begin
        newly_released = '0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            store_released_index[i] = sq_ids[mem_commit.committable_ids[i]];
            store_released[i] = {1'b1, ids[store_released_index[i]]} == {mem_commit.committable[i], mem_commit.committable_ids[i]};
            newly_released |= (CONFIG.SQ_DEPTH'(store_released[i]) << store_released_index[i]);
        end
    end

    always_ff @ (posedge clk) begin
        if (rst)
            released <= '0;
        else
            released <= (released | newly_released) & ~new_request_one_hot;
    end

    assign sq.no_released_stores_pending = ~|(valid & released);

    ////////////////////////////////////////////////////
    //Forwarded Store Data
    always_ff @ (posedge clk) begin
        for (int i=0; i < SNOOP_PORTS; i++)
            wb_snoop_r[i] <= wb_snoop[i];
    end

    logic [31:0] wb_snooped_data [SNOOP_PORTS];

    genvar g;

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_fp_conversion

        //////////// Data input into SQ

        logic [31:0] sq_in_data_fp_conv;

        flopoco_to_ieee_sp direct_to_ieee (
            .clk(clk),
            .X(sq.data_in.data),
            .R(sq_in_data_fp_conv)
        );

        assign sq_in_data_processed = (sq.data_in.is_float)? sq_in_data_fp_conv : sq.data_in.data[31:0];

        /////////// forwarding / snooping of FP values
        logic [31:0] wb_snooped_fp_conv;

        flopoco_to_ieee_sp snoop_to_ieee (
            .clk(clk),
            .X(wb_snoop_r[SNOOP_PORTS_FLOAT_START].data),
            .R(wb_snooped_fp_conv)
        );

        for (g = 0; g < SNOOP_PORTS; g++) begin
            if (g == SNOOP_PORTS_FLOAT_START) // offset, port0 missing
                assign wb_snooped_data[g] = wb_snooped_fp_conv;
            else
                assign wb_snooped_data[g] =  wb_snoop_r[g].data[31:0];
        end

    end else begin
        assign sq_in_data_processed = sq.data_in.data;

        for (g = 0; g < SNOOP_PORTS; g++)
            assign wb_snooped_data[g] =  wb_snoop_r[g].data[31:0];
    end endgenerate

    logic [31:0] selected_snoop_data [2]; // 0: gp, 1: fp. basically muxes between all snoop-ports of same type if there are more than 1 each. Prefers first port. So that there is no undefined data
    logic valid_snoop [2];

    always_comb begin
        selected_snoop_data[0] = '0;
        selected_snoop_data[1] = '0;
        valid_snoop[0] = 0;
        valid_snoop[1] = 0;

        for (int i = 0; i < SNOOP_PORTS; i++) begin
            if (i < SNOOP_PORTS_FLOAT_START) begin
                if (!valid_snoop[0]) begin
                    selected_snoop_data[0] = wb_snooped_data[i];
                    valid_snoop[0] = wb_snoop_r[i].valid && wb_snoop_r[i].id == forward_selector[i].idNeeded;
                end
            end else begin
                if (!valid_snoop[1]) begin
                    selected_snoop_data[1] = wb_snooped_data[i];
                    valid_snoop[1] = wb_snoop_r[i].valid && wb_snoop_r[i].id == forward_selector[i].idNeeded;
                end
            end 
        end
    end

    always_ff @ (posedge clk) begin
        for (int i = 0; i < CONFIG.SQ_DEPTH; i++) begin
            if (sq.push && sq_index == LOG2_SQ_DEPTH'(i)) begin
                data_to_store[i] <= sq_in_data_processed; // possibly reroute through snoop logic, adding a fake snoop port to give it 1 more cycle
                snoop_outstanding[i] <= sq.data_in.forwarded_store;
            end else if (!released[i] && snoop_outstanding[i]) begin
                if (forward_selector[i].isFloat && CONFIG.INCLUDE_FPU_SINGLE) begin
                    if (valid_snoop[1]) begin
                        data_to_store[i] <= selected_snoop_data[1];
                        snoop_outstanding[i] <= 0;
                    end
                end else begin
                    if (valid_snoop[0]) begin
                        data_to_store[i] <= selected_snoop_data[0];
                        snoop_outstanding[i] <= 0;
                    end
                end
            end
        end
    end
    
    ////////////////////////////////////////////////////
    //Store Transaction Outputs
    logic [31:0] data_for_alignment;
    logic [31:0] sq_data;
    sq_internal_t output_entry;
    assign output_entry = sq_entry[sq_oldest];

    always_comb begin
        //Input: ABCD
        //Assuming aligned requests,
        //Possible byte selections: (A/C/D, B/D, C/D, D)
        data_for_alignment = data_to_store[sq_oldest]; // by definition, any forwarded data, was from a previous instruction (in exec order), which needed to have retired before our store (which includes wb)

        sq_data[7:0] = data_for_alignment[7:0];
        sq_data[15:8] = (output_entry.addr[1:0] == 2'b01) ? data_for_alignment[7:0] : data_for_alignment[15:8];
        sq_data[23:16] = (output_entry.addr[1:0] == 2'b10) ? data_for_alignment[7:0] : data_for_alignment[23:16];
        case(output_entry.addr[1:0])
            2'b10 : sq_data[31:24] = data_for_alignment[15:8];
            2'b11 : sq_data[31:24] = data_for_alignment[7:0];
            default : sq_data[31:24] = data_for_alignment[31:24];
        endcase
    end

    assign sq.valid = valid[sq_oldest] & released[sq_oldest];
    assign sq.data_out = '{
        addr : output_entry.addr,
        be : output_entry.be,
        fn3 : output_entry.fn3,
        data : sq_data,
        subunit_id : output_entry.subunit_id,
        is_amo_sc : output_entry.is_amo_sc,
        is_amo_rmw : output_entry.is_amo_rmw,
        amo_op : output_entry.amo_op,
        has_paired_load : output_entry.has_paired_load
    };

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    sq_overflow_assertion:
        assert property (@(posedge clk) disable iff (rst) sq.push |-> (~sq.full | sq.pop)) else $error("sq overflow");
    fifo_underflow_assertion:
        assert property (@(posedge clk) disable iff (rst) sq.pop |-> sq.valid) else $error("sq underflow");


endmodule
