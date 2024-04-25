/*
 * Copyright © 2017, 2018, 2019 Eric Matthews,  Lesley Shannon
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



module cva5

    import cva5_config::*;
    import l2_config_and_types::*;
    import riscv_types::*;
    import cva5_types::*;

    #(
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter EXTERNAL_INSTR_INV_TARGETS = 0
    )

    (
        input logic clk,
        input logic rst,

        local_memory_interface.master instruction_bram,
        local_memory_interface.master data_bram,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master dwishbone,
        wishbone_interface.master iwishbone,

        output trace_outputs_t tr,

        l2_requester_interface.master l2,

        input interrupt_t s_interrupt,
        input interrupt_t m_interrupt,
        instruction_invalidation_interface.distributor external_instr_inv_targets [EXTERNAL_INSTR_INV_TARGETS]
        );

    ////////////////////////////////////////////////////
    //Unit ID Assignment
    //Generate Issue IDs based on configuration options
    //Then assigned to a struct for ease in passing to sub modules

    //Units with writeback
    localparam int unsigned ALU_UNIT_ID = 32'd0;
    localparam int unsigned LS_UNIT_ID = 32'd1;
    localparam int unsigned CSR_UNIT_ID = LS_UNIT_ID + int'(CONFIG.INCLUDE_CSRS);
    localparam int unsigned MUL_UNIT_ID = CSR_UNIT_ID + int'(CONFIG.INCLUDE_MUL);
    localparam int unsigned DIV_UNIT_ID = MUL_UNIT_ID + int'(CONFIG.INCLUDE_DIV);
    localparam int unsigned FP_TO_GP_UNIT_ID = DIV_UNIT_ID + int'(CONFIG.INCLUDE_FPU_SINGLE);
    localparam int unsigned FP_FLW_UNIT_ID = FP_TO_GP_UNIT_ID + int'(CONFIG.INCLUDE_FPU_SINGLE); // needs to be highest priority wb, as no stall capabilities
    localparam int unsigned FP_MAC_UNIT_ID = FP_FLW_UNIT_ID + int'(CONFIG.INCLUDE_FPU_SINGLE);
    localparam int unsigned FP_DIV_UNIT_ID = FP_MAC_UNIT_ID + int'(CONFIG.INCLUDE_FPU_SINGLE);
    localparam int unsigned FP_SHORT_UNIT_ID = FP_DIV_UNIT_ID + int'(CONFIG.INCLUDE_FPU_SINGLE);
    //Non-writeback units
    localparam int unsigned BRANCH_UNIT_ID = FP_SHORT_UNIT_ID + 1;
    localparam int unsigned IEC_UNIT_ID = BRANCH_UNIT_ID + 1;

    //Total number of units
    localparam int unsigned NUM_UNITS = IEC_UNIT_ID + 1; 

    localparam unit_id_param_t UNIT_IDS = '{
        ALU : ALU_UNIT_ID,
        LS : LS_UNIT_ID,
        CSR : CSR_UNIT_ID,
        MUL : MUL_UNIT_ID,
        DIV : DIV_UNIT_ID,
        FP_TO_GP : FP_TO_GP_UNIT_ID,
        // FP results from here
        FP_FLW : FP_FLW_UNIT_ID,
        FP_MAC : FP_MAC_UNIT_ID,
        FP_DIV : FP_DIV_UNIT_ID,
        FP_SHORT : FP_SHORT_UNIT_ID,
        // No results from here
        BR : BRANCH_UNIT_ID,
        IEC : IEC_UNIT_ID
    };

    ////////////////////////////////////////////////////
    //Writeback Port Assignment
    //
    localparam int unsigned NUM_WB_UNITS_GROUP_1 = 1;//ALU
    localparam int unsigned NUM_WB_UNITS_GROUP_2 = 1 + int'(CONFIG.INCLUDE_CSRS) + int'(CONFIG.INCLUDE_MUL) + int'(CONFIG.INCLUDE_DIV) + int'(CONFIG.INCLUDE_FPU_SINGLE);//LS
    localparam int unsigned NUM_WB_UNITS_FP = int'(CONFIG.INCLUDE_FPU_SINGLE) * 4; // 3 FPU pipes with FP results + FLW from loadStore
    localparam int unsigned NUM_WB_UNITS_GP = NUM_WB_UNITS_GROUP_1 + NUM_WB_UNITS_GROUP_2;
    localparam int unsigned NUM_WB_UNITS = NUM_WB_UNITS_GP + NUM_WB_UNITS_FP;

    localparam int unsigned NUM_INSTR_INV_TARGETS = ((CONFIG.INSTRUCTION_COHERENCY)? (int'(CONFIG.INCLUDE_ICACHE) + int'(CONFIG.INCLUDE_BRANCH_PREDICTOR) + EXTERNAL_INSTR_INV_TARGETS) : (0));
    localparam int unsigned INSTR_INV_TARGET_ICACHE = 0;
    localparam int unsigned INSTR_INV_TARGET_BRANCH_PRED = int'(CONFIG.INCLUDE_ICACHE);
    localparam int unsigned INSTR_INV_TARGET_FIRST_EXTERNAL = int'(CONFIG.INCLUDE_ICACHE) + int'(CONFIG.INCLUDE_BRANCH_PREDICTOR);

    localparam rf_params_t RF_CONFIG = get_derived_rf_params(CONFIG);

    ////////////////////////////////////////////////////
    //Connecting Signals
    l1_arbiter_request_interface l1_request[L1_CONNECTIONS-1:0]();
    l1_arbiter_return_interface l1_response[L1_CONNECTIONS-1:0]();
    logic sc_complete;
    logic sc_success;

    branch_predictor_interface bp();
    branch_results_t br_results;
    logic branch_flush;
    logic branch_pending;
    logic potential_branch_exception;
    exception_packet_t br_exception;
    logic branch_exception_is_jump;

    ras_interface ras();

    issue_packet_t issue;
    register_file_issue_interface #(
        .NUM_WB_GROUPS(RF_CONFIG.GP_WB_GROUP_COUNT),
        .READ_PORTS(RF_CONFIG.GP_READ_PORT_COUNT),
        .DATA_WIDTH(32)
    ) gp_rf_issue();

    register_file_issue_interface #(
        .NUM_WB_GROUPS(FP_RF_FIXED_WRITE_PORT_COUNT),
        .READ_PORTS(FP_RF_FIXED_READ_PORT_COUNT),
        .DATA_WIDTH(34)
    ) fp_rf_issue();


    alu_inputs_t alu_inputs;
    load_store_inputs_t ls_inputs;
    branch_inputs_t branch_inputs;
    mul_inputs_t mul_inputs;
    div_inputs_t div_inputs;
    fp_mac_inputs_t fp_mac_inputs;
    fp_div_sqrt_inputs_t fp_div_inputs;
    fp_short_inputs_t fp_short_inputs;
    fp_to_gp_inputs_t fp_to_gp_inputs;
    gc_inputs_t gc_inputs;
    csr_inputs_t csr_inputs;

    unit_issue_interface unit_issue [NUM_UNITS-1:0]();

    unit_writeback_interface #(
        .RESULT_WIDTH(MAX_POSSIBLE_REG_BITS)
    ) unit_wb [NUM_WB_UNITS] ();

    mmu_interface immu();
    mmu_interface dmmu();

    tlb_interface itlb();
    tlb_interface dtlb();
    logic tlb_on;
    logic [ASIDLEN-1:0] asid;

    //Instruction ID/Metadata
        //ID issuing
    id_t pc_id;
    logic pc_id_available;
    logic pc_id_assigned;
    logic [31:0] if_pc;
        //Fetch stage
    id_t fetch_id;
    logic fetch_complete, fetch_flushing;
    logic [31:0] fetch_instruction;
    logic early_branch_flush;
    logic early_branch_flush_ras_adjust;
    fetch_metadata_t fetch_metadata;
        //Decode stage
    logic decode_advance;
    decode_packet_t decode;   
    logic decode_uses_rd_gp;
    logic decode_uses_rd_fp;
    rs_addr_t decode_rd_addr;
    exception_sources_t decode_exception_unit;
    phys_addr_t decode_phys_rd_addr;
    phys_addr_t decode_phys_rs_addr [RF_CONFIG.TOTAL_READ_PORT_COUNT];
    logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] decode_rs_wb_group [RF_CONFIG.TOTAL_READ_PORT_COUNT];

        //ID freeing
    retire_packet_t retire;
    id_t retire_ids [RETIRE_PORTS];
    logic retire_port_valid [RETIRE_PORTS];
    id_t retire_ids_next [RETIRE_PORTS];
    memory_commit_interface mem_commit();
        //Writeback
    wb_packet_t wb_packet [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
    commit_packet_t commit_packet [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
         //Exception
    logic [31:0] next_retiring_pc;
    logic next_retiring_pc_invalid;

    renamer_interface #(
        .NUM_WB_GROUPS(RF_CONFIG.TOTAL_WB_GROUP_COUNT),
        .RF_READ_PORTS(RF_CONFIG.TOTAL_READ_PORT_COUNT)
    ) decode_rename_interface ();

    //Global Control
    exception_interface exception [NUM_EXCEPTION_SOURCES]();
    logic [$clog2(NUM_EXCEPTION_SOURCES)-1:0] current_exception_unit;
    gc_outputs_t gc;
    load_store_status_t load_store_status;
    logic [LOG2_MAX_IDS:0] post_issue_count;
    logic [LOG2_MAX_IDS:0] post_commit_count;

    logic [1:0] current_privilege;
    logic mret;
    logic sret;
    logic [31:0] epc;
    logic [31:0] exception_target_pc;

    logic interrupt_take;
    logic interrupt_pc_capture;
    logic interrupt_pending;

    logic processing_csr;

    //Decode Unit and Fetch Unit
    logic illegal_instruction;
    logic instruction_issued;
    logic instruction_issued_with_rd;
    logic instruction_issued_with_late_result_commit;

    //LS
    wb_packet_t wb_snoop [RF_CONFIG.TOTAL_WB_GROUP_COUNT-1]; // port0 not needed

    // Instr. Invalidation
    instruction_invalidation_interface instr_inv ();
    instruction_invalidation_queued instr_inv_q [(INSTR_INV_TARGET_FIRST_EXTERNAL > 0)? INSTR_INV_TARGET_FIRST_EXTERNAL : 1] ();

    //Trace Interface Signals
    logic tr_early_branch_correction;
    logic tr_operand_stall;
    logic tr_unit_stall;
    logic tr_no_id_stall;
    logic tr_no_instruction_stall;
    logic tr_other_stall;
    logic tr_branch_operand_stall;
    logic tr_alu_operand_stall;
    logic tr_ls_operand_stall;
    logic tr_div_operand_stall;

    logic tr_alu_op;
    logic tr_branch_or_jump_op;
    logic tr_load_op;
    logic tr_store_op;
    logic tr_mul_op;
    logic tr_div_op;
    logic tr_misc_op;
    logic tr_float_op;

    logic tr_instruction_issued_dec;
    logic [31:0] tr_instruction_pc_dec;
    logic [31:0] tr_instruction_data_dec;

    logic tr_branch_correct;
    logic tr_branch_misspredict;
    logic tr_return_correct;
    logic tr_return_misspredict;

    logic tr_br_taken;
    logic tr_br_is_branch;
    logic tr_br_is_return;
    logic tr_br_is_call;
    logic [31:0] tr_branch_target_pc;

    logic tr_load_conflict_delay;
    logic tr_ls_is_peri_access;
    logic tr_memory_stall;

    logic tr_rs1_forwarding_needed;
    logic tr_rs2_forwarding_needed;
    logic tr_rs1_and_rs2_forwarding_needed;

    ////////////////////////////////////////////////////
    //Implementation


    ////////////////////////////////////////////////////
    // Memory Interface
    generate if (CONFIG.INCLUDE_S_MODE || CONFIG.INCLUDE_ICACHE || CONFIG.INCLUDE_DCACHE) begin : gen_l1_arbiter
        l1_arbiter #(.CONFIG(CONFIG))
        arb(
            .clk (clk),
            .rst (rst),
            .l2 (l2),
            .sc_complete (sc_complete),
            .sc_success (sc_success),
            .l1_request (l1_request),
            .l1_response (l1_response)
        );
    end
    endgenerate

    ////////////////////////////////////////////////////
    // ID support
    instruction_metadata_and_id_management #(
        .CONFIG(CONFIG),
        .RF_CONFIG(RF_CONFIG)
    ) id_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .if_pc (if_pc),
        .pc_id_assigned (pc_id_assigned),
        .fetch_id (fetch_id),
        .branch_flush(branch_flush),
        .early_branch_flush (early_branch_flush),
        .fetch_complete (fetch_complete),
        .fetch_flushing (fetch_flushing),
        .fetch_instruction (fetch_instruction),
        .fetch_metadata (fetch_metadata),
        .decode (decode),
        .decode_advance (decode_advance),
        .decode_uses_rd_gp (decode_uses_rd_gp),
        .decode_uses_rd_fp (decode_uses_rd_fp),
        .decode_rd_addr (decode_rd_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_exception_unit (decode_exception_unit),
        .issue (issue),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .instruction_issued_with_late_result_commit(instruction_issued_with_late_result_commit),
        .wb_packet (wb_packet),
        .commit_packet (commit_packet),
        .retire (retire),
        .retire_ids (retire_ids),
        .retire_port_valid (retire_port_valid),
        .retire_ids_next (retire_ids_next),
        .mem_commit(mem_commit),
        .post_issue_count(post_issue_count),
        .post_commit_count(post_commit_count),
        .next_retiring_pc(next_retiring_pc),
        .next_retiring_pc_invalid(next_retiring_pc_invalid),
        .current_exception_unit (current_exception_unit)
    );



    ////////////////////////////////////////////////////
    // Fetch
    fetch # (.CONFIG(CONFIG))
    fetch_block (
        .clk (clk),
        .rst (rst),
        .branch_flush (branch_flush),
        .gc (gc),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .pc_id_assigned (pc_id_assigned),
        .fetch_complete (fetch_complete),
        .fetch_flushing (fetch_flushing),
        .fetch_metadata (fetch_metadata),
        .bp (bp),
        .ras (ras),
        .early_branch_flush (early_branch_flush),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .if_pc (if_pc),
        .fetch_instruction (fetch_instruction),                                
        .instruction_bram (instruction_bram), 
        .iwishbone (iwishbone),
        .icache_on ('1),
        .tlb (itlb), 
        .tlb_on (tlb_on),
        .l1_request (l1_request[L1_ICACHE_ID]), 
        .l1_response (l1_response[L1_ICACHE_ID]), 
        .exception (1'b0),
        .tr_early_branch_correction (tr_early_branch_correction),
        .instr_inv(instr_inv_q[INSTR_INV_TARGET_ICACHE])
    );

    branch_predictor #(.CONFIG(CONFIG))
    bp_block (       
        .clk (clk),
        .rst (rst),
        .bp (bp),
        .br_results (br_results),
        .ras (ras),
        .instr_inv(instr_inv_q[INSTR_INV_TARGET_BRANCH_PRED])
    );

    ras # (.CONFIG(CONFIG))
    ras_block(
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .ras (ras)
    );

    generate if (CONFIG.INCLUDE_S_MODE) begin : gen_itlb_immu

        tlb_lut_ram #(.WAYS(CONFIG.ITLB.WAYS), .DEPTH(CONFIG.ITLB.DEPTH))
        i_tlb (       
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .abort_request (gc.fetch_flush | early_branch_flush),
            .asid (asid),
            .tlb (itlb), 
            .mmu (immu)
        );

        mmu i_mmu (
            .clk (clk),
            .rst (rst),
            .mmu (immu) , 
            .abort_request (gc.fetch_flush),
            .l1_request (l1_request[L1_IMMU_ID]), 
            .l1_response (l1_response[L1_IMMU_ID])
        );

        end
        else begin
            assign itlb.ready = 1;
            assign itlb.done = itlb.new_request;
            assign itlb.physical_address = itlb.virtual_address;
            assign itlb.is_fault = 0;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Renamer
    renamer #(
        .CONFIG(CONFIG),
        .RF_CONFIG(RF_CONFIG)
    ) renamer_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_advance (decode_advance),
        .decode (decode_rename_interface),
        .issue (issue), //packet
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .retire (retire) //packet
    );

    ////////////////////////////////////////////////////
    //Decode/Issue
    decode_and_issue #(
        .CONFIG (CONFIG),
        .NUM_UNITS (NUM_UNITS),
        .UNIT_IDS (UNIT_IDS)
        )
    decode_and_issue_block (
        .clk (clk),
        .rst (rst),
        .pc_id_available (pc_id_available),
        .decode (decode),
        .decode_advance (decode_advance),
        .renamer (decode_rename_interface),
        .decode_uses_rd_gp (decode_uses_rd_gp),
        .decode_uses_rd_fp (decode_uses_rd_fp),
        .decode_rd_addr (decode_rd_addr),
        .decode_exception_unit (decode_exception_unit),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_phys_rs_addr (decode_phys_rs_addr),
        .decode_rs_wb_group (decode_rs_wb_group),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .instruction_issued_with_late_result_commit(instruction_issued_with_late_result_commit),
        .issue (issue),
        .gp_rf (gp_rf_issue),
        .fp_rf (fp_rf_issue),
        .alu_inputs (alu_inputs),
        .ls_inputs (ls_inputs),
        .branch_inputs (branch_inputs),
        .gc_inputs (gc_inputs),
        .csr_inputs (csr_inputs),
        .mul_inputs (mul_inputs),
        .div_inputs (div_inputs),
        .fp_mac_inputs (fp_mac_inputs),
        .fp_div_inputs (fp_div_inputs),
        .fp_short_inputs (fp_short_inputs),
        .fp_to_gp_inputs (fp_to_gp_inputs),
        .unit_issue (unit_issue),
        .gc (gc),
        .current_privilege (current_privilege),
        .exception (exception[PRE_ISSUE_EXCEPTION]),
        .tr_operand_stall (tr_operand_stall),
        .tr_unit_stall (tr_unit_stall),
        .tr_no_id_stall (tr_no_id_stall),
        .tr_no_instruction_stall (tr_no_instruction_stall),
        .tr_other_stall (tr_other_stall),
        .tr_branch_operand_stall (tr_branch_operand_stall),
        .tr_alu_operand_stall (tr_alu_operand_stall),
        .tr_ls_operand_stall (tr_ls_operand_stall),
        .tr_div_operand_stall (tr_div_operand_stall),
        .tr_alu_op (tr_alu_op),
        .tr_branch_or_jump_op (tr_branch_or_jump_op),
        .tr_load_op (tr_load_op),
        .tr_store_op (tr_store_op),
        .tr_mul_op (tr_mul_op),
        .tr_div_op (tr_div_op),
        .tr_misc_op (tr_misc_op),
        .tr_float_op (tr_float_op),
        .tr_instruction_issued_dec (tr_instruction_issued_dec),
        .tr_instruction_pc_dec (tr_instruction_pc_dec),
        .tr_instruction_data_dec (tr_instruction_data_dec)
    );

    ////////////////////////////////////////////////////
    //Register File
    register_file #(
        .WRITE_PORTS(RF_CONFIG.GP_WB_GROUP_COUNT),
        .READ_PORTS(RF_CONFIG.GP_READ_PORT_COUNT),
        .DEPTH(64),
        .DATA_WIDTH(32),
        .ALLOW_WRITE_P0(0),
        .SELF_FLUSH(0) // means we will externally wire up commit port 0 to flush, because conveniently it will already have the addr that needs flushing we will only force the valid bit
    ) regfile_gp (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .decode_phys_rs_addr (decode_phys_rs_addr[RSG1:RSG2]),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .decode_rs_wb_group ('{ decode_rs_wb_group[RSG1][0], decode_rs_wb_group[RSG2][0]}),
        .decode_advance (decode_advance),
        .decode_uses_rd (decode_uses_rd_gp && |decode_phys_rd_addr), // written to and not zero

        .inflight_commit_addr_per_port ('{
            gp_rf_issue.phys_rd_addr, // since wb is combinatorial, commit addr would always be invalid or phys_rd_addr. But phys_rd_addr is also the addr that needs flushing and can never overlap
            commit_packet[1].phys_addr
        }),
        .inflight_commit_per_port ('{
            gp_rf_issue.single_cycle_or_flush, // true when commit[0].valid || flushing neeed (killing an inflight reg after we mistakenly marked it as inflight before the flush)
            commit_packet[1].valid
        }),

        .rf_issue (gp_rf_issue),
        .commit (commit_packet[0:1])
    );

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_fp_regfile
        register_file #(
            .WRITE_PORTS(RF_CONFIG.FP_WB_GROUP_COUNT),
            .READ_PORTS(RF_CONFIG.FP_READ_PORT_COUNT),
            .DEPTH(64),
            .DATA_WIDTH(34),
            .ALLOW_WRITE_P0(1),
            .SELF_FLUSH(1) // the RF will internally mux a toggle port to kill inflight regs with flushes. Otherwise would require 1 more toggle write port just for flushing
        ) regfile_fp (
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .decode_phys_rs_addr (decode_phys_rs_addr[RSF1:RSF3]),
            .decode_phys_rd_addr (decode_phys_rd_addr),
            .decode_rs_wb_group ('{'0, '0, '0}),
            .decode_advance (decode_advance),
            .decode_uses_rd (decode_uses_rd_fp),

            .inflight_commit_addr_per_port ('{
                commit_packet[2].phys_addr
            }),
            .inflight_commit_per_port ('{
                commit_packet[2].valid
            }),

            .rf_issue (fp_rf_issue),
            .commit ('{commit_packet[2]})
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Execution Units
    branch_unit #(.CONFIG(CONFIG))
    branch_unit_block ( 
        .clk (clk),
        .rst (rst),                                    
        .issue (unit_issue[UNIT_IDS.BR]),
        .branch_inputs (branch_inputs),
        .br_results (br_results),
        .branch_flush (branch_flush),
        .branch_pending (branch_pending),
        .exception (exception[BR_EXCEPTION]),
        .tr_branch_correct (tr_branch_correct),
        .tr_branch_misspredict (tr_branch_misspredict),
        .tr_return_correct (tr_return_correct),
        .tr_return_misspredict (tr_return_misspredict),
        .tr_br_is_branch(tr_br_is_branch),
        .tr_br_taken(tr_br_taken),
        .tr_br_is_call(tr_br_is_call),
        .tr_br_is_return(tr_br_is_return),
        .tr_branch_target_pc(tr_branch_target_pc)
    );


    alu_unit alu_unit_block (
        .clk (clk),
        .rst (rst),
        .alu_inputs (alu_inputs),
        .issue (unit_issue[UNIT_IDS.ALU]), 
        .wb (unit_wb[UNIT_IDS.ALU])
    );

    logic instr_inv_enabled;
    logic [NUM_INSTR_INV_TARGETS-1:0] instr_inv_outstanding;
    logic instr_inv_stall;

    generate if (CONFIG.INSTRUCTION_COHERENCY) begin: gen_instr_inv
        instruction_invalidation_interface instr_inv_tgt [INSTR_INV_TARGET_FIRST_EXTERNAL] (); // only allocate for internal ones
        logic [NUM_INSTR_INV_TARGETS-1:0] instr_inv_ready;

        genvar i;
        for (i=0; i < NUM_INSTR_INV_TARGETS; i++) begin : gen_inv_instr_tgt_map
            if (i < INSTR_INV_TARGET_FIRST_EXTERNAL) begin
                assign instr_inv_tgt[i].inv_addr = instr_inv.inv_addr;
                assign instr_inv_tgt[i].inv_valid = instr_inv.inv_valid;
                assign instr_inv_outstanding[i] = instr_inv_tgt[i].inv_outstanding;
                assign instr_inv_ready[i] = instr_inv_tgt[i].inv_ready;

                instruction_invalidation_queue #(
                    .DEPTH(CONFIG.INSTR_INV_QUEUE_DEPTH)
                ) queue (
                    .clk(clk),
                    .rst(rst),
                    .source(instr_inv_tgt[i]),
                    .sink(instr_inv_q[i])
                );

            end else begin
                assign external_instr_inv_targets[i - INSTR_INV_TARGET_FIRST_EXTERNAL].inv_addr = instr_inv.inv_addr;
                assign external_instr_inv_targets[i - INSTR_INV_TARGET_FIRST_EXTERNAL].inv_valid = instr_inv.inv_valid;
                assign instr_inv_outstanding[i] = external_instr_inv_targets[i - INSTR_INV_TARGET_FIRST_EXTERNAL].inv_outstanding;
                assign instr_inv_ready[i] = external_instr_inv_targets[i - INSTR_INV_TARGET_FIRST_EXTERNAL].inv_ready;
            end
        end
        assign instr_inv.inv_ready = &instr_inv_ready;
    end else begin
        assign instr_inv_outstanding = '0; // so that there are no stalls

        assign instr_inv_q[0].inv_valid = '0; // so that icache and branch-pred dont invalidate random stuff
    end
    endgenerate

    unit_writeback_interface #(
        .RESULT_WIDTH(MAX_POSSIBLE_REG_BITS)
    ) ls_unit_fp_wb ();    

    load_store_unit #(
        .CONFIG(CONFIG),
        .RF_CONFIG(RF_CONFIG)
    ) load_store_unit_block (
        .clk (clk),
        .rst (rst),
        .gc (gc),
        .ls_inputs (ls_inputs),
        .issue (unit_issue[UNIT_IDS.LS]),
        .dcache_on (1'b1), 
        .clear_reservation (1'b0), 
        .tlb (dtlb),
        .tlb_on (tlb_on),                            
        .l1_request (l1_request[L1_DCACHE_ID]), 
        .l1_response (l1_response[L1_DCACHE_ID]),
        .sc_complete (sc_complete),
        .sc_success (sc_success),                                       
        .m_axi (m_axi),
        .m_avalon (m_avalon),
        .dwishbone (dwishbone),                                       
        .data_bram (data_bram),
        .wb_snoop (wb_snoop),
        .mem_commit(mem_commit),
        .exception (exception[LS_EXCEPTION]),
        .load_store_status(load_store_status),
        .wb (unit_wb[UNIT_IDS.LS]),
        .wb_fp (ls_unit_fp_wb),
        .tr_load_conflict_delay (tr_load_conflict_delay),
        .tr_ls_is_peri_access(tr_ls_is_peri_access),
        .tr_memory_stall(tr_memory_stall),
        .instr_inv(instr_inv),
        .instr_inv_en(instr_inv_enabled),
        .instr_inv_stall(instr_inv_stall)
    );

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_load_fp
        assign unit_wb[UNIT_IDS.FP_FLW].rd = ls_unit_fp_wb.rd;
        assign unit_wb[UNIT_IDS.FP_FLW].id = ls_unit_fp_wb.id;
        assign unit_wb[UNIT_IDS.FP_FLW].done = ls_unit_fp_wb.done;
        assign ls_unit_fp_wb.ack = unit_wb[UNIT_IDS.FP_FLW].ack;
        assign unit_issue[UNIT_IDS.FP_FLW].ready = 0;
    end endgenerate

    generate if (CONFIG.INCLUDE_S_MODE) begin : gen_dtlb_dmmu
        tlb_lut_ram #(.WAYS(CONFIG.DTLB.WAYS), .DEPTH(CONFIG.DTLB.DEPTH))
        d_tlb (       
            .clk (clk),
            .rst (rst),
            .gc (gc),
            .abort_request (1'b0),
            .asid (asid),
            .tlb (dtlb), 
            .mmu (dmmu)
        );

        mmu d_mmu (
            .clk (clk),
            .rst (rst),
            .mmu (dmmu) , 
            .abort_request (1'b0),
            .l1_request (l1_request[L1_DMMU_ID]), 
            .l1_response (l1_response[L1_DMMU_ID])
        );
    end
    else begin
            assign dtlb.ready = 1;
            assign dtlb.done = dtlb.new_request;
            assign dtlb.physical_address = dtlb.virtual_address;
            assign dtlb.is_fault = 0;
    end
    endgenerate

    generate if (CONFIG.INCLUDE_CSRS) begin : gen_csrs
        csr_unit # (
            .CONFIG(CONFIG),
            .NUM_INSTR_INV_TARGETS(NUM_INSTR_INV_TARGETS)
        ) csr_unit_block (
            .clk(clk),
            .rst(rst),
            .csr_inputs (csr_inputs),
            .issue (unit_issue[UNIT_IDS.CSR]), 
            .wb (unit_wb[UNIT_IDS.CSR]),
            .current_privilege(current_privilege),
            .interrupt_take(interrupt_take),
            .interrupt_pc_capture(interrupt_pc_capture),
            .interrupt_pending(interrupt_pending),
            .processing_csr(processing_csr),
            .tlb_on(tlb_on),
            .asid(asid),
            .immu(immu),
            .dmmu(dmmu),
            .exception(gc.exception),
            .exception_target_pc (exception_target_pc),
            .mret(mret),
            .sret(sret),
            .epc(epc),
            .retire(retire),
            .retire_ids(retire_ids),
            .s_interrupt(s_interrupt),
            .m_interrupt(m_interrupt),
            .instr_inv_enabled(instr_inv_enabled),
            .instr_inv_ready(instr_inv.inv_ready),
            .instr_inv_outstanding(instr_inv_outstanding)
        );
    end else begin
        assign instr_inv_enabled = 0;
    end
    endgenerate

    gc_unit #(.CONFIG(CONFIG))
    gc_unit_block (
        .clk (clk),
        .rst (rst),
        .issue (unit_issue[UNIT_IDS.IEC]),
        .gc_inputs (gc_inputs),
        .branch_flush (branch_flush),
        .branch_pending (branch_pending),
        .exception (exception),
        .exception_target_pc (exception_target_pc),
        .current_exception_unit (current_exception_unit),
        .gc (gc),
        .next_retiring_pc(next_retiring_pc),
        .next_retiring_pc_invalid(next_retiring_pc_invalid),
        .mret(mret),
        .sret(sret),
        .epc(epc),
        .retire_ids_next (retire_ids_next),
        .interrupt_take(interrupt_take),
        .interrupt_pc_capture(interrupt_pc_capture),
        .interrupt_pending(interrupt_pending),
        .processing_csr(processing_csr),
        .load_store_status(load_store_status),
        .post_issue_count (post_issue_count),
        .post_commit_count(post_commit_count)
    );

    generate if (CONFIG.INCLUDE_MUL) begin : gen_mul
        mul_unit mul_unit_block (
            .clk (clk),
            .rst (rst),
            .mul_inputs (mul_inputs),
            .issue (unit_issue[UNIT_IDS.MUL]),
            .wb (unit_wb[UNIT_IDS.MUL])
        );
    end endgenerate

    generate if (CONFIG.INCLUDE_DIV) begin : gen_div
        div_unit div_unit_block (
            .clk (clk),
            .rst (rst),
            .div_inputs (div_inputs),
            .issue (unit_issue[UNIT_IDS.DIV]), 
            .wb (unit_wb[UNIT_IDS.DIV])
        );
    end endgenerate

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_fpu
        fp_to_gp_unit_sp fp_to_gp_unit (
            .clk(clk),
            .rst(rst),
            .inputs(fp_to_gp_inputs),
            .issue(unit_issue[UNIT_IDS.FP_TO_GP]),
            .wb(unit_wb[UNIT_IDS.FP_TO_GP])
        );

        fp_mac_unit_sp fp_mac_unit (
            .clk(clk),
            .rst(rst),
            .inputs(fp_mac_inputs),
            .issue(unit_issue[UNIT_IDS.FP_MAC]),
            .wb(unit_wb[UNIT_IDS.FP_MAC])
        );

        fp_div_sqrt_unit_sp fp_div_unit (
            .clk(clk),
            .rst(rst),
            .inputs(fp_div_inputs),
            .issue(unit_issue[UNIT_IDS.FP_DIV]),
            .wb(unit_wb[UNIT_IDS.FP_DIV])
        );

        fp_short_unit_sp fp_short_unit (
            .clk(clk),
            .rst(rst),
            .inputs(fp_short_inputs),
            .issue(unit_issue[UNIT_IDS.FP_SHORT]),
            .wb(unit_wb[UNIT_IDS.FP_SHORT])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Writeback
    //First writeback port: ALU
    //Second writeback port: LS, CSR, [MUL], [DIV], [FP_TP_GP] // LS needs to be first, will not stall on missing ack
    //Third write port: [FP_FLW], [FP_MAC], [FP_DIV], [FP_SHORT] / LS needs to be first, will not stall on missing ack
    localparam int unsigned NUM_WB_UNITS_PER_PORT [MAX_WB_GROUPS] = '{NUM_WB_UNITS_GROUP_1, NUM_WB_UNITS_GROUP_2, NUM_WB_UNITS_FP};
    writeback #(
        .CONFIG (CONFIG),
        .RF_CONFIG(RF_CONFIG),
        .NUM_WB_UNITS_PER_PORT (NUM_WB_UNITS_PER_PORT),
        .NUM_WB_UNITS (NUM_WB_UNITS)
    )
    writeback_block (
        .clk (clk),
        .rst (rst),
        .wb_packet (wb_packet),
        .unit_wb (unit_wb),
        .wb_snoop (wb_snoop)
    );

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    //Ensure that reset is held for at least 32 cycles to clear shift regs
    // always_ff @ (posedge clk) begin
    //     assert property(@(posedge clk) $rose (rst) |=> rst[*32]) else $error("Reset not held for long enough!");
    // end

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin : gen_cva5_trace
        always_ff @(posedge clk) begin
            tr.events.early_branch_correction <= tr_early_branch_correction;
            tr.events.operand_stall <= tr_operand_stall;
            tr.events.unit_stall <= tr_unit_stall;
            tr.events.no_id_stall <= tr_no_id_stall;
            tr.events.no_instruction_stall <= tr_no_instruction_stall;
            tr.events.other_stall <= tr_other_stall;
            tr.events.instruction_issued_dec <= tr_instruction_issued_dec;
            tr.events.branch_operand_stall <= tr_branch_operand_stall;
            tr.events.alu_operand_stall <= tr_alu_operand_stall;
            tr.events.ls_operand_stall <= tr_ls_operand_stall;
            tr.events.div_operand_stall <= tr_div_operand_stall;
            tr.events.alu_op <= tr_alu_op;
            tr.events.branch_or_jump_op <= tr_branch_or_jump_op;
            tr.events.load_op <= tr_load_op;
            tr.events.store_op <= tr_store_op;
            tr.events.mul_op <= tr_mul_op;
            tr.events.div_op <= tr_div_op;
            tr.events.misc_op <= tr_misc_op;
            tr.events.float_op <= tr_float_op;
            tr.events.branch_correct <= tr_branch_correct;
            tr.events.branch_misspredict <= tr_branch_misspredict;
            tr.events.return_correct <= tr_return_correct;
            tr.events.return_misspredict <= tr_return_misspredict;
            tr.events.load_conflict_delay <= tr_load_conflict_delay;
            tr.events.rs1_forwarding_needed <= tr_rs1_forwarding_needed;
            tr.events.rs2_forwarding_needed <= tr_rs2_forwarding_needed;
            tr.events.rs1_and_rs2_forwarding_needed <= tr_rs1_and_rs2_forwarding_needed;
            tr.events.instr_inv_stall <= instr_inv_stall;
            tr.events.br_branch_taken <= tr_br_taken;
            tr.events.br_is_branch <= tr_br_is_branch;
            tr.events.br_is_return <= tr_br_is_return;
            tr.events.br_is_call <= tr_br_is_call;
            tr.events.ls_is_peri_access <= tr_ls_is_peri_access;
            tr.events.memory_stall <= tr_memory_stall;
            tr.current_privilege <= current_privilege;
            tr.branch_target_pc <= tr_branch_target_pc;
            tr.instruction_pc_dec <= tr_instruction_pc_dec;
            tr.instruction_data_dec <= tr_instruction_data_dec;
        end
    end
    endgenerate

endmodule
