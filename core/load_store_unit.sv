/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module load_store_unit

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

        input load_store_inputs_t ls_inputs,
        unit_issue_interface.unit issue,

        input logic dcache_on,
        input logic clear_reservation,
        tlb_interface.requester tlb,
        input logic tlb_on,

        l1_arbiter_request_interface.master l1_request,
        l1_arbiter_return_interface.master l1_response,
        input sc_complete,
        input sc_success,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master dwishbone,

        local_memory_interface.master data_bram,

        //Writeback-Store Interface
        input wb_packet_t wb_snoop [RF_CONFIG.TOTAL_WB_GROUP_COUNT-1], // port0 ignored, writes immediately

        // interface to id_unit for committing of memory ops and tracking
        memory_commit_interface.ls mem_commit,

        exception_interface.unit exception,
        output load_store_status_t load_store_status,
        unit_writeback_interface.unit wb,
        unit_writeback_interface.unit wb_fp,

		// Trace
        output logic tr_load_conflict_delay,
        output logic tr_ls_is_peri_access,
        output logic tr_memory_stall,

        // Instruction Invalidation
        instruction_invalidation_interface.source instr_inv,
        input logic instr_inv_en,
        output logic instr_inv_stall
    );

    localparam NUM_SUB_UNITS = int'(CONFIG.INCLUDE_DLOCAL_MEM) + int'(CONFIG.INCLUDE_PERIPHERAL_BUS) + int'(CONFIG.INCLUDE_DCACHE);
    localparam NUM_SUB_UNITS_W = (NUM_SUB_UNITS == 1) ? 1 : $clog2(NUM_SUB_UNITS+1);

    localparam ILLEGAL_SUBUNIT_ID = 0;
    localparam LOCAL_MEM_ID = int'(CONFIG.INCLUDE_DLOCAL_MEM);
    localparam BUS_ID = CONFIG.INCLUDE_PERIPHERAL_BUS? 1 + int'(CONFIG.INCLUDE_DLOCAL_MEM) : 0;
    localparam DCACHE_ID = CONFIG.INCLUDE_DCACHE? (1 + int'(CONFIG.INCLUDE_DLOCAL_MEM) + int'(CONFIG.INCLUDE_PERIPHERAL_BUS)) : 0;

    //Should be equal to pipeline depth of longest load/store subunit 
    localparam ATTRIBUTES_DEPTH = 2;//CONFIG.INCLUDE_DCACHE ? 2 : 1;

    //Subunit signals
    addr_utils_interface #(CONFIG.DLOCAL_MEM_ADDR.L, CONFIG.DLOCAL_MEM_ADDR.H) dlocal_mem_addr_utils ();
    addr_utils_interface #(CONFIG.PERIPHERAL_BUS_ADDR.L, CONFIG.PERIPHERAL_BUS_ADDR.H) dpbus_addr_utils ();
    addr_utils_interface #(CONFIG.DCACHE_ADDR.L, CONFIG.DCACHE_ADDR.H) dcache_addr_utils ();
    memory_sub_unit_interface sub_unit[NUM_SUB_UNITS:0]();

    addr_utils_interface #(CONFIG.DCACHE.NON_CACHEABLE.L, CONFIG.DCACHE.NON_CACHEABLE.H) uncacheable_utils ();

    logic [NUM_SUB_UNITS:1] sub_unit_address_match;
    logic [NUM_SUB_UNITS:0] sub_unit_loads_non_destructive;

    data_access_shared_inputs_t shared_inputs;
    logic [31:0] unit_data_array [NUM_SUB_UNITS:0];
    logic [NUM_SUB_UNITS:1] unit_ready;
    logic [NUM_SUB_UNITS:0] unit_data_valid;
    logic [NUM_SUB_UNITS_W-1:0] last_unit;
    logic [NUM_SUB_UNITS_W-1:0] current_unit;

    logic units_ready;

    logic unit_switch;
    logic unit_switch_in_progress;
    logic unit_switch_hold;

    logic sub_unit_issue;
    logic load_complete;
    logic float_load_complete;

    logic [31:0] virtual_address;
    logic [31:0] physical_address;
    logic [NUM_SUB_UNITS_W-1:0] input_subunit_id;

    logic [31:0] unit_muxed_load_data;
    logic [31:0] aligned_load_data;
    logic [31:0] final_load_data;
    logic [FLEN_INTERNAL-1:0] final_float_load_data;


    logic unaligned_addr;
    logic unmatched_addr;
    logic load_exception_complete;
    logic fence_hold;
    logic amo_hold;

    typedef struct packed{
        logic is_halfword;
        logic is_signed;
        logic [1:0] byte_addr;
        logic [1:0] final_mux_sel;
        id_t id;
        logic is_float;
        logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    } load_attributes_t;
    load_attributes_t  mem_attr, wb_attr;

    logic [3:0] be;
    //FIFOs
    fifo_interface #(.DATA_WIDTH($bits(load_attributes_t))) load_attributes();

    load_store_queue_interface lsq();
    logic tr_possible_load_conflict_delay;
    logic unit_idle;
    logic amo_hold_completed;

    ////////////////////////////////////////////////////
    //Implementation
    ////////////////////////////////////////////////////


    ////////////////////////////////////////////////////
    // Exceptions
    generate if (CONFIG.INCLUDE_M_MODE) begin : gen_ls_exceptions
        logic new_exception;
        exception_code_t exception_code;

        always_comb begin
            case(ls_inputs.fn3)
                LS_H_fn3, L_HU_fn3 : unaligned_addr = virtual_address[0];
                LS_W_fn3 : unaligned_addr = |virtual_address[1:0];
                default : unaligned_addr = 0;
            endcase

            casez ({ls_inputs.store, unmatched_addr, unaligned_addr})
                3'b01? : exception_code = LOAD_FAULT;
                3'b11? : exception_code = STORE_AMO_FAULT;
                3'b101 : exception_code = STORE_AMO_ADDR_MISSALIGNED;
                default : exception_code = LOAD_ADDR_MISSALIGNED;
            endcase

        end

        assign unmatched_addr = input_subunit_id == ILLEGAL_SUBUNIT_ID;
        //TODO access faults if subunit == 0

        assign new_exception = (unaligned_addr || unmatched_addr) & issue.new_request & ~ls_inputs.fence;
        always_ff @(posedge clk) begin
            if (rst)
                exception.valid <= 0;
            else
                exception.valid <= (exception.valid & ~exception.ack) | new_exception;
        end

        always_ff @(posedge clk) begin
            if (new_exception & ~exception.valid) begin
                exception.code <= exception_code;
                exception.tval <= physical_address;
                exception.id <= issue.id;
            end
        end

        always_ff @(posedge clk) begin
            if (rst)
                load_exception_complete <= 0;
            else
                load_exception_complete <= exception.valid & exception.ack & (exception.code inside {LOAD_ADDR_MISSALIGNED, LOAD_FAULT});
        end
    end else begin
       assign unaligned_addr = 0;
       assign unmatched_addr = 0; 
    end endgenerate

    ////////////////////////////////////////////////////
    //Load-Store status
    assign unit_idle = lsq.empty & (~load_attributes.valid) & units_ready;
    assign load_store_status = '{
        sq_empty : lsq.sq_empty,
        no_commited_ops_pending : lsq.no_released_stores_pending || (load_attributes.valid && sub_unit_loads_non_destructive[wb_attr.subunit_id]),
        idle : unit_idle
    };


    ////////////////////////////////////////////////////
    //TLB interface
    assign virtual_address = ls_inputs.rs1 + 32'(signed'(ls_inputs.offset));

    assign tlb.virtual_address = virtual_address;
    assign tlb.new_request = tlb_on & issue.new_request;
    assign tlb.execute = 0;
    assign tlb.rnw = ls_inputs.load & ~ls_inputs.store;

    assign physical_address = tlb_on ? tlb.physical_address : virtual_address;

    ////////////////////////////////////////////////////
    //Byte enable generation
    //Only set on store
    //  SW: all bytes
    //  SH: upper or lower half of bytes
    //  SB: specific byte
    always_comb begin
        be = 0;
        case(ls_inputs.fn3[1:0])
            LS_B_fn3[1:0] : be[virtual_address[1:0]] = 1;
            LS_H_fn3[1:0] : begin
                be[virtual_address[1:0]] = 1;
                be[{virtual_address[1], 1'b1}] = 1;
            end
            default : be = '1;
        endcase
    end

    ////////////////////////////////////////////////////
    //Load Store Queue

    one_hot_to_integer #(NUM_SUB_UNITS+1)
    sub_unit_select (
        .one_hot ({sub_unit_address_match, 1'b0}), 
        .int_out (input_subunit_id)
    );

    assign lsq.data_in = '{
        addr : physical_address,
        fn3 : ls_inputs.fn3,
        be : be,
        data : ls_inputs.rs2,
        load : ls_inputs.load,
        store : ls_inputs.store,
        loads_non_destructive : sub_unit_loads_non_destructive[input_subunit_id],
        is_float : ls_inputs.is_float,
        id : issue.id,
        subunit_id : input_subunit_id,
        forwarded_store : ls_inputs.forwarded_store,
        id_needed : ls_inputs.store_forward_id,
        amo : ls_inputs.amo
    };

    assign lsq.potential_push = issue.possible_issue;
    assign lsq.push = issue.new_request & ~unaligned_addr & ~unmatched_addr & (~tlb_on | tlb.done) & ~ls_inputs.fence;

    load_store_queue  # (
        .CONFIG(CONFIG),
        .RF_CONFIG(RF_CONFIG)
    ) lsq_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .lsq (lsq),
        .wb_snoop (wb_snoop),
        .mem_commit(mem_commit),
        .tr_possible_load_conflict_delay (tr_possible_load_conflict_delay)
    );
    assign shared_inputs = lsq.data_out;
    assign lsq.pop = sub_unit_issue;


    ////////////////////////////////////////////////////
    //Unit tracking
    assign current_unit = shared_inputs.subunit_id;

    always_ff @ (posedge clk) begin
        if (load_attributes.push)
            last_unit <= current_unit;
    end

    //When switching units, ensure no outstanding loads so that there can be no timing collisions with results
    assign unit_switch = (current_unit != last_unit) & load_attributes.valid;
    always_ff @ (posedge clk) begin
        if (rst)
            unit_switch_in_progress <= 0;
        else
            unit_switch_in_progress <= (unit_switch_in_progress | unit_switch) & ~load_attributes.valid;
    end
    assign unit_switch_hold = unit_switch | unit_switch_in_progress;

    ////////////////////////////////////////////////////
    //Primary Control Signals
    assign units_ready = &unit_ready & (~unit_switch_hold) & (~instr_inv_stall);
    assign load_complete = (CONFIG.INCLUDE_FPU_SINGLE && !wb_attr.is_float) && |unit_data_valid;

    assign issue.ready = (~tlb_on | tlb.ready) & (~lsq.full) & (~fence_hold) & (~amo_hold) & (~exception.valid);
    assign sub_unit_issue = lsq.valid & units_ready;

    assign amo_hold_completed = lsq.sq_empty || (lsq.valid && shared_inputs.store && shared_inputs.amo.is_release); // would be for a store with RL semantics, but all stores are in execution-order anyways so should never cause a hold

    always_ff @ (posedge clk) begin
        if (rst) begin
            fence_hold <= 0;
            amo_hold <= 0;
        end else begin
            fence_hold <= (fence_hold && ~load_store_status.idle) || (issue.new_request && ls_inputs.fence);
            // this is for acquire and release on AMO ops. Stores and loads will each retire in execution order, so all stores will always be aq&rl with other stores (and loads with other loads).
            // Acquire/Release only cares about observable changes to memory, so only stores. Only problem for us is acquire on LR, which requires all existing stores to retire first. 
            // Release on LR is discouraged by the spec and does not have to do anything. 
            amo_hold <= (amo_hold && ~amo_hold_completed) || (issue.new_request && ls_inputs.amo.is_acquire && ls_inputs.amo.is_lr);
        end
    end

    ////////////////////////////////////////////////////
    //Load attributes FIFO
    logic [NUM_SUB_UNITS_W-1:0] subunit_id;
    logic already_committed_load;
    assign already_committed_load = lsq.valid && !sub_unit_loads_non_destructive[shared_inputs.subunit_id] && shared_inputs.load;
    assign subunit_id = (!gc.writeback_suppress || already_committed_load)? shared_inputs.subunit_id : '0; // if suppressing, force illegal subUnit, which will immediately return a random result, instead of requesting from any subUnit
    logic [1:0] final_mux_sel;

    always_comb begin
        case(shared_inputs.fn3)
            LS_B_fn3, L_BU_fn3 : final_mux_sel = 0;
            LS_H_fn3, L_HU_fn3 : final_mux_sel = 1;
            default : final_mux_sel = 2; //LS_W_fn3
        endcase
    end
    
    assign mem_attr = '{
        is_halfword : shared_inputs.fn3[0],
        is_signed : ~|shared_inputs.fn3[2:1],
        is_float : shared_inputs.is_float,
        byte_addr : shared_inputs.addr[1:0],
        final_mux_sel : final_mux_sel,
        id : shared_inputs.id,
        subunit_id : subunit_id
    };

    assign load_attributes.data_in = mem_attr;
    assign load_attributes.push = sub_unit_issue && shared_inputs.load;
    assign load_attributes.potential_push = load_attributes.push;
    
    cva5_fifo #(.DATA_WIDTH($bits(load_attributes_t)), .FIFO_DEPTH(ATTRIBUTES_DEPTH))
    attributes_fifo (
        .clk (clk),
        .rst (rst), 
        .fifo (load_attributes)
    );

    assign load_attributes.pop = load_complete || float_load_complete;
    assign wb_attr = load_attributes.data_out;

    assign mem_commit.committed_id = shared_inputs.id;
    assign mem_commit.committed = sub_unit_issue && shared_inputs.load; // these loads can lead to ISA-visible changes in peripherals. This is point-of-no-return. They must retire after commit. If it is unsure, whether this op should retire, then you committed it to early

    ////////////////////////////////////////////////////
    //Unit Instantiation
    
    // dummy values for subunit_id 0, which is an illegal access
    assign sub_unit_loads_non_destructive[0] = 1;
    assign unit_data_valid[0] = gc.writeback_suppress && load_attributes.valid && wb_attr.subunit_id == 0;
    assign unit_data_array[0] = 32'hCDCDCDCD;

    generate
        for (genvar i=0; i <= NUM_SUB_UNITS; i++) begin : gen_subunit_inputs
            assign sub_unit[i].new_request = sub_unit_issue & subunit_id == NUM_SUB_UNITS_W'(i);
            assign sub_unit[i].addr = shared_inputs.addr;
            assign sub_unit[i].re = shared_inputs.load;
            assign sub_unit[i].we = shared_inputs.store;
            assign sub_unit[i].be = shared_inputs.be;
            assign sub_unit[i].data_in = shared_inputs.data_in;
        end
        for (genvar i=1; i <= NUM_SUB_UNITS; i++) begin : gen_sub_unit_outputs
            assign unit_ready[i] = sub_unit[i].ready;
            assign unit_data_valid[i] = sub_unit[i].data_valid;
            assign unit_data_array[i] = sub_unit[i].data_out;
        end
    endgenerate

    generate if (CONFIG.INCLUDE_DLOCAL_MEM) begin : gen_ls_local_mem
        assign sub_unit_loads_non_destructive[LOCAL_MEM_ID] = 1;
        assign sub_unit_address_match[LOCAL_MEM_ID] = dlocal_mem_addr_utils.address_range_check(physical_address);

        local_mem_sub_unit #(
            .INCLUDE_AMO(CONFIG.INCLUDE_AMO)
        ) d_local_mem (
            .clk (clk), 
            .rst (rst),
            .unit (sub_unit[LOCAL_MEM_ID]),
            .local_mem (data_bram),
            .amo (shared_inputs.amo)
        );
        end
    endgenerate

    generate if (CONFIG.INCLUDE_PERIPHERAL_BUS) begin : gen_ls_pbus
            assign sub_unit_loads_non_destructive[BUS_ID] = 1;
            assign sub_unit_address_match[BUS_ID] = dpbus_addr_utils.address_range_check(physical_address);

            if(CONFIG.PERIPHERAL_BUS_TYPE == AXI_BUS)
                axi_master axi_bus (
                    .clk (clk),
                    .rst (rst),
                    .m_axi (m_axi),
                    .size ({1'b0,shared_inputs.fn3[1:0]}),
                    .ls (sub_unit[BUS_ID])
                ); //Lower two bits of fn3 match AXI specification for request size (byte/halfword/word)
            else if (CONFIG.PERIPHERAL_BUS_TYPE == WISHBONE_BUS)
                wishbone_master wishbone_bus (
                    .clk (clk),
                    .rst (rst),
                    .wishbone (dwishbone),
                    .ls (sub_unit[BUS_ID])
                );
            else if (CONFIG.PERIPHERAL_BUS_TYPE == AVALON_BUS)  begin
                avalon_master avalon_bus (
                    .clk (clk),
                    .rst (rst),
                    .m_avalon (m_avalon), 
                    .ls (sub_unit[BUS_ID])
                );
            end
        end
    endgenerate

    generate
        if (CONFIG.INCLUDE_DCACHE) begin : gen_ls_dcache
            logic uncacheable;
            assign sub_unit_loads_non_destructive[DCACHE_ID] = 1;
            assign sub_unit_address_match[DCACHE_ID] = dcache_addr_utils.address_range_check(physical_address);
            assign uncacheable = uncacheable_utils.address_range_check(shared_inputs.addr);

            dcache # (.CONFIG(CONFIG))
            data_cache (
                .clk (clk),
                .rst (rst),
                .dcache_on (dcache_on),
                .l1_request (l1_request),
                .l1_response (l1_response),
                .sc_complete (sc_complete),
                .sc_success (sc_success),
                .clear_reservation (clear_reservation),
                .amo (shared_inputs.amo),
                .uncacheable (uncacheable),
                .ls (sub_unit[DCACHE_ID])
            );

            assign instr_inv.inv_addr = sub_unit[DCACHE_ID].addr[31:2];

            if (CONFIG.INSTRUCTION_COHERENCY) begin: gen_ls_inv_source
                assign instr_inv_stall = instr_inv_en & shared_inputs.store & ~instr_inv.inv_ready;
                assign instr_inv.inv_valid = instr_inv_en & sub_unit[DCACHE_ID].we & sub_unit[DCACHE_ID].new_request;
            end else begin
                assign instr_inv_stall = '0;
                assign instr_inv.inv_valid = '0;
            end
        end else begin
            assign instr_inv.inv_valid = '0;
            assign instr_inv_stall = 0;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Output Muxing
    logic sign_bit_data [4];
    logic [1:0] sign_bit_sel;
    logic sign_bit;
    
    assign unit_muxed_load_data = unit_data_array[wb_attr.subunit_id];

    //Byte/halfword select: assumes aligned operations
    assign aligned_load_data[31:16] = unit_muxed_load_data[31:16];
    assign aligned_load_data[15:8] = wb_attr.byte_addr[1] ? unit_muxed_load_data[31:24] : unit_muxed_load_data[15:8];
    assign aligned_load_data[7:0] = unit_muxed_load_data[wb_attr.byte_addr*8 +: 8];

    assign sign_bit_data = '{unit_muxed_load_data[7], unit_muxed_load_data[15], unit_muxed_load_data[23], unit_muxed_load_data[31]};
    assign sign_bit_sel = wb_attr.byte_addr | {1'b0, wb_attr.is_halfword};
    assign sign_bit = wb_attr.is_signed & sign_bit_data[sign_bit_sel];

    //Sign extending
    always_comb begin
        case(wb_attr.final_mux_sel)
            0 : final_load_data = {{24{sign_bit}}, aligned_load_data[7:0]};
            1 : final_load_data = {{16{sign_bit}}, aligned_load_data[15:0]};
            default : final_load_data = aligned_load_data; //LS_W_fn3
        endcase
    end

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_to_fp_conversion

        ieee_to_flopoco_sp to_flopoco (
            .clk(clk),
            .X(unit_muxed_load_data),
            .R(final_float_load_data)
        );

        assign float_load_complete = (CONFIG.INCLUDE_FPU_SINGLE && wb_attr.is_float) && |unit_data_valid; // delay complete here if conversion requires an additional cycle
    end else begin

        assign final_float_load_data = 0;
        assign float_load_complete = 0;

    end endgenerate

    ////////////////////////////////////////////////////
    //Output bank
    assign wb.rd[31:0] = final_load_data;
    assign wb.done = load_complete || (load_exception_complete && !wb_attr.is_float);
    assign wb.id = load_exception_complete ? exception.id : wb_attr.id;

    assign wb_fp.rd = final_float_load_data;
    assign wb_fp.done = float_load_complete || (load_exception_complete && wb_attr.is_float);
    assign wb_fp.id = load_exception_complete ? exception.id : wb_attr.id;

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    spurious_load_complete_assertion:
        assert property (@(posedge clk) disable iff (rst) load_complete |-> (load_attributes.valid && unit_data_valid[wb_attr.subunit_id]))
        else $error("Spurious load complete detected!");

    `ifdef ENABLE_SIMULATION_ASSERTIONS
        invalid_ls_address_assertion:
            assert property (@(posedge clk) disable iff (rst) (sub_unit_issue & ~ls_inputs.fence) |-> subunit_id != ILLEGAL_SUBUNIT_ID)
            else $error("invalid L/S address 0x%x, load: %d, store: %d", shared_inputs.addr, shared_inputs.load, shared_inputs.store);

        amo_on_peri:
            assert property (@(posedge clk) disable iff (rst) (sub_unit_issue && ~ls_inputs.fence && CONFIG.INCLUDE_PERIPHERAL_BUS && subunit_id == NUM_SUB_UNITS_W'(BUS_ID))
                        |-> (!shared_inputs.amo.is_lr && !shared_inputs.amo.is_sc && !shared_inputs.amo.is_rmw))
            else $error("amo operation on peripheral bus at 0x%x, load: %d, store: %d, isLr: %d, isSc: %d, isRmw: %d, amoOp: 0x%x", shared_inputs.addr, shared_inputs.load, shared_inputs.store, shared_inputs.amo.is_lr, shared_inputs.amo.is_sc, shared_inputs.amo.is_rmw, shared_inputs.amo.op);
    `endif

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin : gen_ls_trace
        assign tr_load_conflict_delay = tr_possible_load_conflict_delay & units_ready;
        assign tr_ls_is_peri_access = CONFIG.INCLUDE_PERIPHERAL_BUS && input_subunit_id == NUM_SUB_UNITS_W'(BUS_ID);
        // coarse. triggers whenever dcache is not immediately ready (cannot write or even request load) or takes more than 1 cycle to respond to a load
        assign tr_memory_stall = CONFIG.INCLUDE_DCACHE && ((load_attributes.valid && wb_attr.subunit_id == NUM_SUB_UNITS_W'(DCACHE_ID) && !unit_data_valid[DCACHE_ID] && !sub_unit_issue) || (lsq.valid && shared_inputs.subunit_id == NUM_SUB_UNITS_W'(DCACHE_ID) && !unit_ready[DCACHE_ID]));
    end
    endgenerate

endmodule
