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

import taiga_config::*;
import riscv_types::*;
import taiga_types::*;

module taiga (
        input logic clk,
        input logic rst,

        local_memory_interface.master instruction_bram,
        local_memory_interface.master data_bram,

        axi_interface.master m_axi,
        avalon_interface.master m_avalon,
        wishbone_interface.master m_wishbone,

        output trace_outputs_t tr,

        l2_requester_interface.master l2,

        input logic timer_interrupt,
        input logic interrupt
        );

    l1_arbiter_request_interface l1_request[L1_CONNECTIONS-1:0]();
    l1_arbiter_return_interface l1_response[L1_CONNECTIONS-1:0]();
    logic sc_complete;
    logic sc_success;

    branch_predictor_interface bp();
    branch_results_t br_results;
    logic branch_flush;
    logic potential_branch_exception;
    exception_packet_t br_exception;
    logic branch_exception_is_jump;

    ras_interface ras();

    issue_packet_t issue;
    register_file_issue_interface rf_issue();


    alu_inputs_t alu_inputs;
    load_store_inputs_t ls_inputs;
    branch_inputs_t branch_inputs;
    mul_inputs_t mul_inputs;
    div_inputs_t div_inputs;
    gc_inputs_t gc_inputs;

    unit_issue_interface unit_issue [NUM_UNITS-1:0]();

    exception_packet_t  ls_exception;
    logic ls_exception_is_store;

    unit_writeback_interface unit_wb  [NUM_WB_UNITS]();

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
    logic fetch_complete;
    logic [31:0] fetch_instruction;
    logic early_branch_flush;
    logic early_branch_flush_ras_adjust;
    fetch_metadata_t fetch_metadata;
        //Decode stage
    logic decode_advance;
    decode_packet_t decode;   
    logic decode_uses_rd;
    rs_addr_t decode_rd_addr;
     phys_addr_t decode_phys_rd_addr;
        //Branch predictor
    id_t branch_id;
    branch_metadata_t branch_metadata_if;
    branch_metadata_t branch_metadata_ex;
        //ID freeing
    retire_packet_t retire;
    id_t retire_ids [RETIRE_PORTS];
    logic retire_ids_retired [RETIRE_PORTS];
        //Writeback
    wb_packet_t wb_packet [NUM_WB_GROUPS];
    commit_packet_t commit_packet [NUM_WB_GROUPS];
         //Exception
    id_t exception_id;
    logic [31:0] exception_pc;

    renamer_interface decode_rename_interface ();

    //Global Control
    logic gc_init_clear;
    logic gc_fetch_hold;
    logic gc_issue_hold;
    logic gc_issue_flush;
    logic gc_fetch_flush;
    logic gc_fetch_pc_override;
    logic gc_supress_writeback;
    logic gc_tlb_flush;
    logic [31:0] gc_fetch_pc;
    logic ls_is_idle;
    logic [LOG2_MAX_IDS:0] post_issue_count;

    //Decode Unit and Fetch Unit
    logic illegal_instruction;
    logic instruction_issued;
    logic instruction_issued_with_rd;
    logic gc_flush_required;

    //LS
    wb_packet_t wb_snoop;

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

    logic tr_instruction_issued_dec;
    logic [31:0] tr_instruction_pc_dec;
    logic [31:0] tr_instruction_data_dec;

    logic tr_branch_correct;
    logic tr_branch_misspredict;
    logic tr_return_correct;
    logic tr_return_misspredict;

    logic tr_load_conflict_delay;

    logic tr_rs1_forwarding_needed;
    logic tr_rs2_forwarding_needed;
    logic tr_rs1_and_rs2_forwarding_needed;

    unit_id_t tr_num_instructions_completing;
    id_t tr_num_instructions_in_flight;
    id_t tr_num_of_instructions_pending_writeback;
    ////////////////////////////////////////////////////
    //Implementation


    ////////////////////////////////////////////////////
    // Memory Interface
    generate if (ENABLE_S_MODE || USE_ICACHE || USE_DCACHE)

        l1_arbiter arb(
            .clk (clk),
            .rst (rst),
            .l2 (l2),
            .sc_complete (sc_complete),
            .sc_success (sc_success),
            .l1_request (l1_request),
            .l1_response (l1_response)
        );

    endgenerate

    ////////////////////////////////////////////////////
    // ID support
    instruction_metadata_and_id_management id_block (
        .clk (clk),
        .rst (rst),
        .gc_init_clear (gc_init_clear),
        .gc_fetch_flush (gc_fetch_flush),
        .pc_id (pc_id),
        .pc_id_available (pc_id_available),
        .if_pc (if_pc),
        .pc_id_assigned (pc_id_assigned),
        .fetch_id (fetch_id),
        .early_branch_flush (early_branch_flush),
        .fetch_complete (fetch_complete),
        .fetch_instruction (fetch_instruction),
        .fetch_metadata (fetch_metadata),
        .decode (decode),
        .decode_advance (decode_advance),
        .decode_uses_rd (decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .issue (issue),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .branch_metadata_if (branch_metadata_if),
        .branch_metadata_ex (branch_metadata_ex),
        .branch_id (branch_id),
        .wb_packet (wb_packet),
        .commit_packet (commit_packet),
        .retire (retire),
        .retire_ids (retire_ids),
        .retire_ids_retired(retire_ids_retired),
        .post_issue_count(post_issue_count),
        .exception_id (exception_id),
        .exception_pc (exception_pc)
    );

    ////////////////////////////////////////////////////
    // Fetch
    fetch fetch_block (
        .clk (clk),
        .rst (rst),
        .branch_flush (branch_flush),
        .gc_fetch_hold (gc_fetch_hold),
        .gc_fetch_flush (gc_fetch_flush),
        .gc_fetch_pc_override (gc_fetch_pc_override),
        .gc_fetch_pc (gc_fetch_pc),           
        .pc_id_available (pc_id_available),
        .pc_id_assigned (pc_id_assigned),
        .fetch_complete (fetch_complete),
        .fetch_metadata (fetch_metadata),
        .bp (bp),
        .ras (ras),
        .early_branch_flush (early_branch_flush),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .if_pc (if_pc),
        .fetch_instruction (fetch_instruction),                                
        .instruction_bram (instruction_bram), 
        .icache_on ('1),
        .tlb (itlb), 
        .tlb_on (tlb_on),
        .l1_request (l1_request[L1_ICACHE_ID]), 
        .l1_response (l1_response[L1_ICACHE_ID]), 
        .exception (1'b0),
        .tr_early_branch_correction (tr_early_branch_correction)
    );

    branch_predictor bp_block (       
       .clk (clk),
       .rst (rst),
       .bp (bp),
       .branch_metadata_if (branch_metadata_if),
       .branch_metadata_ex (branch_metadata_ex),
       .br_results (br_results)
    );

    ras ras_block(
        .clk (clk),
        .rst (rst),
        .gc_fetch_flush (gc_fetch_flush),
        .early_branch_flush_ras_adjust (early_branch_flush_ras_adjust),
        .ras (ras)
    );

    generate if (ENABLE_S_MODE) begin

        tlb_lut_ram #(ITLB_WAYS, ITLB_DEPTH) i_tlb (       
            .clk (clk),
            .rst (rst),
            .abort_request (gc_fetch_flush | early_branch_flush),
            .gc_tlb_flush (gc_tlb_flush),
            .asid (asid),
            .tlb (itlb), 
            .mmu (immu)
        );

        mmu i_mmu (
            .clk (clk),
            .rst (rst),
            .mmu (immu) , 
            .abort_request (gc_fetch_flush),
            .l1_request (l1_request[L1_IMMU_ID]), 
            .l1_response (l1_response[L1_IMMU_ID])
        );

        end
        else begin
            assign itlb.ready = 1;
            assign itlb.done = itlb.new_request;
            assign itlb.physical_address = itlb.virtual_address;
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Renamer
    renamer renamer_block (
        .clk (clk),
        .rst (rst),
        .gc_init_clear (gc_init_clear),
        .gc_fetch_flush (gc_fetch_flush),
        .decode_advance (decode_advance),
        .decode (decode_rename_interface),
        .issue (issue), //packet
        .retire (retire) //packet
    );

    ////////////////////////////////////////////////////
    //Decode/Issue
    decode_and_issue decode_and_issue_block (
        .clk (clk),
        .rst (rst),
        .pc_id_available (pc_id_available),
        .decode (decode),
        .decode_advance (decode_advance),
        .renamer (decode_rename_interface),
        .decode_uses_rd (decode_uses_rd),
        .decode_rd_addr (decode_rd_addr),
        .decode_phys_rd_addr (decode_phys_rd_addr),
        .instruction_issued (instruction_issued),
        .instruction_issued_with_rd (instruction_issued_with_rd),
        .issue (issue),
        .rf (rf_issue),
        .alu_inputs (alu_inputs),
        .ls_inputs (ls_inputs),
        .branch_inputs (branch_inputs),
        .gc_inputs (gc_inputs),
        .mul_inputs (mul_inputs),
        .div_inputs (div_inputs),
        .unit_issue (unit_issue),
        .gc_fetch_hold (gc_fetch_hold),
        .gc_issue_hold (gc_issue_hold),
        .gc_fetch_flush (gc_fetch_flush),
        .gc_issue_flush (gc_issue_flush),
        .gc_flush_required (gc_flush_required),
        .illegal_instruction (illegal_instruction),
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
        .tr_instruction_issued_dec (tr_instruction_issued_dec),
        .tr_instruction_pc_dec (tr_instruction_pc_dec),
        .tr_instruction_data_dec (tr_instruction_data_dec)
    );

    ////////////////////////////////////////////////////
    //Register File
    register_file register_file_block (
        .clk (clk),
        .rst (rst),
        .gc_init_clear (gc_init_clear),
        .rf_issue (rf_issue),
        .commit (commit_packet)
    );

    ////////////////////////////////////////////////////
    //Execution Units
    branch_unit branch_unit_block ( 
        .clk (clk),
        .rst (rst),                                    
        .issue (unit_issue[BRANCH_UNIT_ID]),
        .branch_inputs (branch_inputs),
        .br_results (br_results),
        .ras (ras),
        .branch_flush (branch_flush),
        .branch_id (branch_id),
        .branch_metadata_ex (branch_metadata_ex),
        .potential_branch_exception (potential_branch_exception),
        .branch_exception_is_jump (branch_exception_is_jump),
        .br_exception (br_exception),
        .tr_branch_correct (tr_branch_correct),
        .tr_branch_misspredict (tr_branch_misspredict),
        .tr_return_correct (tr_return_correct),
        .tr_return_misspredict (tr_return_misspredict)
    );


    alu_unit alu_unit_block (
        .clk (clk),
        .rst (rst),
        .alu_inputs (alu_inputs),
        .issue (unit_issue[ALU_UNIT_ID]), 
        .wb (unit_wb[ALU_UNIT_ID])
    );

    load_store_unit load_store_unit_block (
        .clk (clk),
        .rst (rst),
        .ls_inputs (ls_inputs),
        .issue (unit_issue[LS_UNIT_ID]),
        .dcache_on (1'b1), 
        .clear_reservation (1'b0), 
        .tlb (dtlb),  
        .gc_fetch_flush (gc_fetch_flush),
        .gc_issue_flush (gc_issue_flush),           
        .tlb_on (tlb_on),                            
        .l1_request (l1_request[L1_DCACHE_ID]), 
        .l1_response (l1_response[L1_DCACHE_ID]),
        .sc_complete (sc_complete),
        .sc_success (sc_success),                                       
        .m_axi (m_axi),
        .m_avalon (m_avalon),
        .m_wishbone (m_wishbone),                                       
        .data_bram (data_bram),
        .wb_snoop (wb_snoop),
        .retire_ids (retire_ids),
        .retire_ids_retired(retire_ids_retired),
        .ls_is_idle (ls_is_idle),
        .ls_exception (ls_exception),
        .ls_exception_is_store (ls_exception_is_store),
        .wb (unit_wb[LS_UNIT_ID]),
        .tr_load_conflict_delay (tr_load_conflict_delay)
    );

    generate if (ENABLE_S_MODE) begin
        tlb_lut_ram #(DTLB_WAYS, DTLB_DEPTH) d_tlb (       
            .clk (clk),
            .rst (rst),
            .abort_request (1'b0),
            .gc_tlb_flush (gc_tlb_flush),
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
    end
    endgenerate

    gc_unit gc_unit_block (
        .clk (clk),
        .rst (rst),
        .issue (unit_issue[GC_UNIT_ID]),
        .gc_inputs (gc_inputs),
        .gc_flush_required (gc_flush_required),
        .branch_flush (branch_flush),
        .potential_branch_exception (potential_branch_exception),
        .branch_exception_is_jump (branch_exception_is_jump),
        .br_exception (br_exception),
        .illegal_instruction (illegal_instruction),
        .ls_exception (ls_exception),
        .ls_exception_is_store (ls_exception_is_store),
        .tlb_on (tlb_on),
        .asid (asid),
        .immu (immu),
        .dmmu (dmmu),
        .exception_id (exception_id),
        .exception_pc (exception_pc),
        .retire (retire),
        .interrupt (interrupt),
        .timer_interrupt (timer_interrupt),
        .gc_init_clear (gc_init_clear),
        .gc_fetch_hold (gc_fetch_hold),
        .gc_issue_hold (gc_issue_hold),
        .gc_issue_flush (gc_issue_flush),
        .gc_fetch_flush (gc_fetch_flush),
        .gc_fetch_pc_override (gc_fetch_pc_override),
        .gc_supress_writeback (gc_supress_writeback),
        .gc_tlb_flush (gc_tlb_flush),
        .gc_fetch_pc (gc_fetch_pc),
        .ls_is_idle (ls_is_idle),
        .post_issue_count (post_issue_count),
        .wb (unit_wb[GC_UNIT_ID])
    );

    generate if (USE_MUL)
        mul_unit mul_unit_block (.*,
            .clk (clk),
            .rst (rst),
            .mul_inputs (mul_inputs),
            .issue (unit_issue[MUL_UNIT_ID]),
            .wb (unit_wb[MUL_UNIT_ID])
        );
    endgenerate

    generate if (USE_DIV)
        div_unit div_unit_block (
            .clk (clk),
            .rst (rst),
            .gc_fetch_flush (gc_fetch_flush),
            .div_inputs (div_inputs),
            .issue (unit_issue[DIV_UNIT_ID]), 
            .wb (unit_wb[DIV_UNIT_ID])
        );
    endgenerate

    ////////////////////////////////////////////////////
    //Writeback
    writeback writeback_block (
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
    generate if (ENABLE_TRACE_INTERFACE) begin
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
            tr.events.branch_correct <= tr_branch_correct;
            tr.events.branch_misspredict <= tr_branch_misspredict;
            tr.events.return_correct <= tr_return_correct;
            tr.events.return_misspredict <= tr_return_misspredict;
            tr.events.load_conflict_delay <= tr_load_conflict_delay;
            tr.events.rs1_forwarding_needed <= tr_rs1_forwarding_needed;
            tr.events.rs2_forwarding_needed <= tr_rs2_forwarding_needed;
            tr.events.rs1_and_rs2_forwarding_needed <= tr_rs1_and_rs2_forwarding_needed;
            tr.events.num_instructions_completing <= tr_num_instructions_completing;
            tr.events.num_instructions_in_flight <= tr_num_instructions_in_flight;
            tr.events.num_of_instructions_pending_writeback <= tr_num_of_instructions_pending_writeback;
            tr.instruction_pc_dec <= tr_instruction_pc_dec;
            tr.instruction_data_dec <= tr_instruction_data_dec;
        end
    end
    endgenerate

endmodule
