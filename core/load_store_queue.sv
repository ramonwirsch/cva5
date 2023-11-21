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

module load_store_queue //ID-based input buffer for Load/Store Unit

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
        input gc_outputs_t gc,

        load_store_queue_interface.queue lsq,
        //Writeback snooping
        input wb_packet_t wb_snoop [RF_CONFIG.TOTAL_WB_GROUP_COUNT-1], // port0 ignored, writes immediately

        // interface to id_unit for committing of memory ops and tracking
        memory_commit_interface.ls mem_commit,

        output logic tr_possible_load_conflict_delay
    );

    typedef struct packed {
        logic [31:0] addr;
        logic [2:0] fn3;
        logic is_float;
        id_t id;
        logic [1:0] subunit_id;
        logic [CONFIG.SQ_DEPTH-1:0] potential_store_conflicts;
        logic is_amo_lr;
        logic has_paired_store;
    } lq_entry_t;

    addr_hash_t addr_hash;
    logic [CONFIG.SQ_DEPTH-1:0] potential_store_conflicts;
    sq_entry_t sq_entry;
    logic store_conflict;
    logic load_selected;
    logic fused_load_and_store;

    lq_entry_t lq_data_in;
    lq_entry_t lq_data_out;

    fifo_interface #(.DATA_WIDTH($bits(lq_entry_t))) lq();
    store_queue_interface sq();
    ////////////////////////////////////////////////////
    //Implementation

    //Can accept requests so long as store queue is not needed or is not full
    assign lsq.full = lsq.data_in.store & sq.full;

    //Address hash for load-store collision checking
    addr_hash lsq_addr_hash (
        .clk (clk),
        .rst (rst | gc.memq_flush),
        .addr (lsq.data_in.addr),
        .addr_hash (addr_hash)
    );

    ////////////////////////////////////////////////////
    //Load Queue
    cva5_fifo #(.DATA_WIDTH($bits(lq_entry_t)), .FIFO_DEPTH(MAX_IDS))
    load_queue_fifo (
        .clk(clk),
        .rst(rst), // cannot reset for flush, need to playback all id's for renamer to not loose track of registers
        .fifo(lq)
    );

    //FIFO control signals
    assign lq.push = lsq.push & lsq.data_in.load;
    assign lq.potential_push = lsq.potential_push;
    assign lq.pop = lsq.pop && (load_selected || fused_load_and_store);

    //FIFO data ports
    assign lq_data_in = '{
        addr : lsq.data_in.addr,
        fn3 : lsq.data_in.fn3,
        is_float : lsq.data_in.is_float,
        id : lsq.data_in.id, 
        subunit_id : lsq.data_in.subunit_id,
        potential_store_conflicts : potential_store_conflicts,
        is_amo_lr : lsq.data_in.amo.is_lr,
        has_paired_store : lsq.data_in.store || !lsq.data_in.loads_non_destructive // will only be pushed if marked as load
    };
    assign lq.data_in = lq_data_in;
    assign lq_data_out = lq.data_out;
    ////////////////////////////////////////////////////
    //Store Queue
    assign sq.push = lsq.push && (lsq.data_in.store || (!lsq.data_in.loads_non_destructive && lsq.data_in.load));
    assign sq.pop = lsq.pop && (~load_selected || fused_load_and_store);
    assign sq.data_in = lsq.data_in;

    store_queue  # (
        .CONFIG(CONFIG),
        .RF_CONFIG(RF_CONFIG)
    ) sq_block (
        .clk (clk),
        .rst (rst | gc.memq_flush),
        .lq_push (lq.push),
        .lq_pop (lq.pop),
        .sq (sq),
        .addr_hash (addr_hash),
        .potential_store_conflicts (potential_store_conflicts),
        .prev_store_conflicts (lq_data_out.potential_store_conflicts),
        .store_conflict (store_conflict),
        .wb_snoop (wb_snoop),
        .mem_commit(mem_commit)
    );

    ////////////////////////////////////////////////////
    //Output
    //Priority is for loads over stores.
    //A store will be selected only if either no loads are ready // (OR if the store queue is full and a store is ready TODO does not match code below, no reason given)
    // For ops that MUST await retire, but include load-aspects, like AMO RMW ops like amoadd or Peri-Loads, fuse matching load and store queue entries together.
    // When fusing, does not technically matter whether load is selected or not, both will be valid and overlap
    assign load_selected = lq.valid && ~store_conflict && !lq_data_out.has_paired_store;// & ~(sq_full & sq.valid); // writeback_suppress means we are emptying the pipelines and all transactions that have not been issued to memory are irrelevant
    // will empty out the load queue while suppressing, still need to reply wb_packets with correct ids, for id_block and renamer to not get confused
    assign fused_load_and_store = sq.valid && sq.data_out.has_paired_load && lq.valid && lq_data_out.has_paired_store;

    assign lsq.valid = load_selected || (sq.valid && !sq.data_out.has_paired_load) || fused_load_and_store;
    assign lsq.data_out = '{
        addr : load_selected ? lq_data_out.addr : sq.data_out.addr,
        load : load_selected || fused_load_and_store,
        store : (!fused_load_and_store && !load_selected) || (fused_load_and_store && |sq.data_out.be),
        be : load_selected ? '0 : sq.data_out.be,
        fn3 : load_selected ? lq_data_out.fn3 : sq.data_out.fn3,
        is_float : load_selected ? lq_data_out.is_float : sq.data_out.is_float,
        data_in : sq.data_out.data,
        id : lq_data_out.id,
        subunit_id : load_selected ? lq_data_out.subunit_id : sq.data_out.subunit_id,
        amo : '{
            is_lr : lq_data_out.is_amo_lr,
            is_sc : sq.data_out.is_amo_sc,
            is_rmw : sq.data_out.is_amo_rmw,
            is_acquire : 0,
            is_release : 0,
            op : sq.data_out.amo_op
        }
    };

    assign lsq.sq_empty = sq.empty;
    assign lsq.no_released_stores_pending = sq.no_released_stores_pending;
    assign lsq.empty = ~lq.valid & sq.empty;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin : gen_lsq_trace
        assign tr_possible_load_conflict_delay = lq.valid & (store_conflict | (sq.full & sq.valid));
    end
    endgenerate

endmodule
