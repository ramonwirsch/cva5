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

module instruction_metadata_and_id_management

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

        //Fetch
        output id_t pc_id,
        output logic pc_id_available,
        input logic [31:0] if_pc,
        input logic pc_id_assigned,

        output id_t fetch_id,
        input logic branch_flush,
        input logic early_branch_flush,
        input logic fetch_complete,
        input logic [31:0] fetch_instruction,
        input fetch_metadata_t fetch_metadata,

        //Decode ID
        output decode_packet_t decode,
        input logic decode_advance,
        input logic decode_uses_rd_gp,
        input logic decode_uses_rd_fp,
        input rs_addr_t decode_rd_addr,
        input exception_sources_t decode_exception_unit,
        //renamer
        input phys_addr_t decode_phys_rd_addr,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued,
        input logic instruction_issued_with_rd,
        input logic instruction_issued_with_late_result_commit,

        //WB
        input wb_packet_t wb_packet [RF_CONFIG.TOTAL_WB_GROUP_COUNT],
        output commit_packet_t commit_packet [RF_CONFIG.TOTAL_WB_GROUP_COUNT],

        //Retirer
        output retire_packet_t retire,
        output id_t retire_ids [RETIRE_PORTS],
        output id_t retire_ids_next [RETIRE_PORTS],
        output logic retire_port_valid [RETIRE_PORTS],
        
        memory_commit_interface.state mem_commit,

        //CSR
        output logic [LOG2_MAX_IDS:0] post_issue_count,
        output logic [LOG2_MAX_IDS:0] post_commit_count,
        //Exception
        output logic [31:0] next_retiring_pc,
        output logic next_retiring_pc_invalid,
        output logic [$clog2(NUM_EXCEPTION_SOURCES)-1:0] current_exception_unit
    );
    //////////////////////////////////////////
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] pc_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] instruction_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] valid_fetch_addr_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) phys_addr_t phys_addr_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] uses_rd_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] has_late_result_commit_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(fetch_metadata_t)-1:0] fetch_metadata_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(exception_sources_t)-1:0] exception_unit_table [MAX_IDS];

    id_t decode_id;
    id_t issued_id;
    id_t oldest_pre_issue_id;

    localparam ID_COUNTER_W = LOG2_MAX_IDS+1;
    logic [LOG2_MAX_IDS:0] fetched_count_neg;
    logic [LOG2_MAX_IDS:0] pre_issue_count;
    logic [LOG2_MAX_IDS:0] pre_issue_count_next;
    logic [LOG2_MAX_IDS:0] post_issue_count_next;
    logic [LOG2_MAX_IDS:0] post_commit_count_next;
    logic [LOG2_MAX_IDS:0] inflight_count;

    retire_packet_t retire_next;
    logic retire_port_valid_next [RETIRE_PORTS];
    logic id_with_sideffect_committable_next [RETIRE_PORTS];
    logic precommit_suppress;
    logic post_commit_retire;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Instruction Metadata
    //PC table
    //Number of read ports = 1 or 2 (decode stage + exception logic (if enabled))
    always_ff @ (posedge clk) begin
        if (pc_id_assigned)
            pc_table[pc_id] <= if_pc;
    end

    ////////////////////////////////////////////////////
    //Instruction table
    //Number of read ports = 1 (decode stage)
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            instruction_table[fetch_id] <= fetch_instruction;
    end

    ////////////////////////////////////////////////////
    //Valid fetched address table
    //Number of read ports = 1 (decode stage)
    always_ff @ (posedge clk) begin
        if (fetch_complete)
            fetch_metadata_table[fetch_id] <= fetch_metadata;
    end

    ////////////////////////////////////////////////////
    //Phys rd table
    //Number of read ports = (NUM_WB_GROUPS - 1)  (ALU WB group uses issue_phys_rd_addr)
    always_ff @ (posedge clk) begin
        if (decode_advance)
            phys_addr_table[decode_id] <= decode_phys_rd_addr;
    end

    ////////////////////////////////////////////////////
    //Uses rd table
    //Number of read ports = RETIRE_PORTS
    always_ff @ (posedge clk) begin
        if (decode_advance)
            uses_rd_table[decode_id] <= (decode_uses_rd_gp && |decode_rd_addr) || decode_uses_rd_fp;
    end

    always_ff @ (posedge clk) begin
        if (instruction_issued)
            has_late_result_commit_table[issue.id] <= instruction_issued_with_late_result_commit;
    end

    ////////////////////////////////////////////////////
    //Exception unit table
    always_ff @ (posedge clk) begin
        if (decode_advance)
            exception_unit_table[decode_id] <= decode_exception_unit;
    end

    ////////////////////////////////////////////////////
    //ID Management
    
    //Next ID always increases, except on a fetch buffer flush.
    //On a fetch buffer flush, the next ID is restored to the oldest non-issued ID (decode or issue stage)
    //This prevents a stall in the case where all  IDs are either in-flight or
    //in the fetch buffer at the point of a fetch flush.
    always_ff @ (posedge clk) begin
        if (rst)
            oldest_pre_issue_id <= 0;
        else if (instruction_issued)
            oldest_pre_issue_id <= oldest_pre_issue_id + 1;
    end

    always_ff @ (posedge clk) begin
        if (gc.fetch_flush) begin
            pc_id <= oldest_pre_issue_id;
            fetch_id <= oldest_pre_issue_id;
            decode_id <= oldest_pre_issue_id;
        end
        else begin
            pc_id <= (early_branch_flush ? fetch_id : pc_id) + LOG2_MAX_IDS'(pc_id_assigned);
            fetch_id <= fetch_id + LOG2_MAX_IDS'(fetch_complete);
            decode_id <= decode_id + LOG2_MAX_IDS'(decode_advance);
        end
    end
    //Retire IDs
    //Each retire port lags behind the previous one by one index (eg. [3, 2, 1, 0])
     generate for (i = 0; i < RETIRE_PORTS; i++) begin :gen_retire_ids
        always_ff @ (posedge clk) begin
            if (rst)
                retire_ids_next[i] <= LOG2_MAX_IDS'(i);
            else
                retire_ids_next[i] <= retire_ids_next[i] + LOG2_MAX_IDS'(retire_next.count);
        end

        always_ff @ (posedge clk) begin
            if (~gc.retire_hold)
                retire_ids[i] <= retire_ids_next[i];
        end
        
    end endgenerate

    //Represented as a negative value so that the MSB indicates that the decode stage is valid
    always_ff @ (posedge clk) begin
        if (gc.fetch_flush)
            fetched_count_neg <= 0;
        else
            fetched_count_neg <= fetched_count_neg + ID_COUNTER_W'(decode_advance) - ID_COUNTER_W'(fetch_complete);
    end

    //Full instruction count split into two: pre-issue and post-issue
    //pre-issue count can be cleared on a fetch flush
    //post-issue count decremented only on retire
    assign pre_issue_count_next = pre_issue_count  + ID_COUNTER_W'(pc_id_assigned) - ID_COUNTER_W'(instruction_issued);
    always_ff @ (posedge clk) begin
        if (gc.fetch_flush)
            pre_issue_count <= 0;
        else
            pre_issue_count <= pre_issue_count_next;
    end

    assign post_issue_count_next = post_issue_count + ID_COUNTER_W'(instruction_issued) - ID_COUNTER_W'(retire_next.count);
    always_ff @ (posedge clk) begin
        if (rst)
            post_issue_count <= 0;
        else
            post_issue_count <= post_issue_count_next;
    end

    assign post_commit_count_next = post_commit_count + ID_COUNTER_W'(mem_commit.committed) - ID_COUNTER_W'(post_commit_retire);

    always_ff @(posedge clk) begin
        if (rst)
            post_commit_count <= 0;
        else
            post_commit_count <= post_commit_count_next;
    end

    always_ff @ (posedge clk) begin
        if (gc.fetch_flush)
            inflight_count <= post_issue_count_next;
        else
            inflight_count <= pre_issue_count_next + post_issue_count_next;
    end

    ////////////////////////////////////////////////////
    //ID in-use determination
    logic id_waiting_for_writeback [RETIRE_PORTS];
    //WB group zero is not included as it completes within a single cycle
    // Need to await instruction actually completing to retire the insn, because technically, exceptions can occurr up until this point
    // Ops that do not have a result can only throw exceptions early, when they would have had no chance to retire already

    id_t inflight_notify_addrs [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
    logic inflight_notify [RF_CONFIG.TOTAL_WB_GROUP_COUNT];

    assign inflight_notify_addrs[0] = issue.id;
    assign inflight_notify[0] = instruction_issued_with_rd && issue.is_multicycle;

    generate for (i=1; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin : gen_inflight_toggle
        assign inflight_notify_addrs[i] = wb_packet[i].id;
        assign inflight_notify[i] = wb_packet[i].valid;
    end endgenerate

    toggle_memory_set # (
        .DEPTH (MAX_IDS),
        .NUM_WRITE_PORTS (RF_CONFIG.TOTAL_WB_GROUP_COUNT), // -1 for port0 (alu) excluded, +1 for marking newly issued ops as inflight
        .NUM_READ_PORTS (RETIRE_PORTS),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_waiting_for_writeback_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc.init_clear),
        .toggle (inflight_notify),
        .toggle_addr (inflight_notify_addrs),
        .read_addr (retire_ids_next),
        .in_use (id_waiting_for_writeback)
    );

    ////////////////////////////////////////////////////
    // late result commit
    // Ops, like Memory Loads that may have destructive side effects cannot be reverted after they have been committed. They must not be suppressed after that point, as that would loose state (looking at you interrupts)
    // But they may not commit immediately after issueing (there is a queue and we may also wait for the op to be front-of-the-line for retiring, because only then is it ensured that no controlflow will divert from it)
    // This bit is set, while the op is still uncommitted and no waiting_for_writeback state is set
    // at the same time as this bit is cleared, either by aborting or committing, the waiting_for_writeback must be decided
    // ops
    logic id_uncommitted [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS-1:0] phys_id_sel;

    toggle_memory_set #(
        .DEPTH (MAX_IDS),
        .NUM_WRITE_PORTS (3), // 1 to mark as uncommitted on issue, 1 to mark as committed by ls_unit, 1 to mark to clear in case we abort prior to commit
        .NUM_READ_PORTS (RETIRE_PORTS),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_uncommitted_toggle_mem_set (
        .clk (clk),
        .rst (rst),
        .init_clear (gc.init_clear),
        .toggle ('{instruction_issued_with_late_result_commit, mem_commit.committed, precommit_suppress}),
        .toggle_addr ('{issue.id, mem_commit.committed_id, retire_ids_next[phys_id_sel]}),
        .read_addr (retire_ids_next),
        .in_use (id_uncommitted)
    );


    ////////////////////////////////////////////////////
    //Retirer
    logic contiguous_retire;
    logic id_is_post_issue [RETIRE_PORTS];
    logic id_ready_to_retire [RETIRE_PORTS];
    logic retire_id_has_late_result_commit [RETIRE_PORTS];
    logic [RETIRE_PORTS-1:0] retire_id_uses_rd;

     generate for (i = 0; i < RETIRE_PORTS; i++) begin : gen_retire_writeback
        assign retire_id_uses_rd[i] = uses_rd_table[retire_ids_next[i]];
        assign retire_id_has_late_result_commit[i] = has_late_result_commit_table[retire_ids_next[i]];
     end endgenerate

    //Supports retiring up to RETIRE_PORTS instructions.  The retired block of instructions must be
    //contiguous and must start with the first retire port.  Additionally, only one register file writing 
    //instruction is supported per cycle (because Renamer can only process one destination reg change per cycle. CSR unit also depends on the write being in retire_port[0]).
    //If an exception is pending, only retire a single intrustuction per cycle.  As such, the pending
    //exception will have to become the oldest instruction retire_ids[0] before it can retire.
    logic retire_with_rd_found;
    logic suppress_retire_id [RETIRE_PORTS];
    logic post_commit_retires [RETIRE_PORTS];
    logic late_result_committable [RETIRE_PORTS];
    always_comb begin
        contiguous_retire = 1;
        retire_with_rd_found = 0;
        post_commit_retire = 0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            id_is_post_issue[i] = post_issue_count > ID_COUNTER_W'(i);

            id_ready_to_retire[i] = id_is_post_issue[i] && (!retire_id_uses_rd[i] || !retire_with_rd_found) && contiguous_retire && ~gc.retire_hold;
            retire_port_valid_next[i] = id_ready_to_retire[i] && ~id_waiting_for_writeback[i] && (!retire_id_has_late_result_commit[i] || !id_uncommitted[i]);
            late_result_committable[i] = retire_id_has_late_result_commit[i] && id_ready_to_retire[i] && ~gc.writeback_suppress && id_uncommitted[i]; // when it is in the front of the line for retiring, then we know, no other controlflow/exceptions etc can happen and it safe to commit destructive memory ops (stores, peri-loads)
            //TODO probably need another signal to tell ls_unit that it needs to release the op to clear inflight-lock in RF without actually changing memory contents
            id_with_sideffect_committable_next[i] = late_result_committable[i] || retire_port_valid_next[i];

            suppress_retire_id[i] = retire_id_has_late_result_commit[i] && id_ready_to_retire[i] && gc.writeback_suppress && id_uncommitted[i]; // we can only abort 1 uncommitted per cycle. id_uncommitted implies late_result_commit, which implies uses_rd, which means retire_port_valid_next will only true for 1 port
            post_commit_retires[i] = retire_id_has_late_result_commit[i] && retire_port_valid_next[i] && !id_uncommitted[i];
     
            retire_with_rd_found |= retire_port_valid_next[i] & retire_id_uses_rd[i];
            contiguous_retire &= retire_port_valid_next[i] & ~gc.exception_pending;
            post_commit_retire |= post_commit_retires[i];
        end
    end

    //retire_next packet
    priority_encoder #(.WIDTH(RETIRE_PORTS))
    phys_id_sel_encoder (
        .priority_vector (retire_id_uses_rd),
        .encoded_result (phys_id_sel)
    );
    assign retire_next.phys_id = retire_ids_next[phys_id_sel];
    assign retire_next.valid = retire_with_rd_found;
    assign precommit_suppress = suppress_retire_id[phys_id_sel];

    always_comb begin
        retire_next.count = 0;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            retire_next.count += retire_port_valid_next[i];
        end
    end

    always_ff @ (posedge clk) begin
        retire.valid <= retire_next.valid;
        retire.phys_id <= retire_next.phys_id;
        retire.count <= gc.writeback_suppress ? '0 : retire_next.count;
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            retire_port_valid[i] <= retire_port_valid_next[i] & ~gc.writeback_suppress;
            mem_commit.committable[i] <= id_with_sideffect_committable_next[i];
        end
    end

    assign mem_commit.committable_ids = retire_ids;

    ////////////////////////////////////////////////////
    //Outputs
    assign pc_id_available = ~inflight_count[LOG2_MAX_IDS];

    //Decode
    assign decode.id = decode_id;
    assign decode.valid = fetched_count_neg[LOG2_MAX_IDS];
    assign decode.pc = pc_table[decode_id];
    assign decode.instruction = instruction_table[decode_id];
    assign decode.fetch_metadata = CONFIG.INCLUDE_M_MODE ? fetch_metadata_table[decode_id] : '{ok : 1, error_code : INST_ACCESS_FAULT};

    //Writeback/Commit support
    phys_addr_t commit_phys_addr [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
    assign commit_phys_addr[0] = issue.phys_rd_addr;
     generate for (i = 1; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin : gen_commit_phys_addr
        assign commit_phys_addr[i] = phys_addr_table[wb_packet[i].id];
     end endgenerate

     generate for (i = 0; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin : gen_commit_packet
        assign commit_packet[i].id = wb_packet[i].id;
        assign commit_packet[i].phys_addr = commit_phys_addr[i];        
        assign commit_packet[i].valid = wb_packet[i].valid & |commit_phys_addr[i];
        assign commit_packet[i].data = wb_packet[i].data;
     end endgenerate

    //Exception Support
     generate if (CONFIG.INCLUDE_M_MODE) begin : gen_id_exception_support
        logic branch_flush_r;

        assign next_retiring_pc = branch_flush_r? if_pc : pc_table[retire_ids_next[0]]; // if we just flushed away all valid insns, the next retiring has to be the target of branch_flush, which by this time should be in if_pc (if not reliably, cache)
        assign next_retiring_pc_invalid = retire_port_valid_next[0] && retire_id_uses_rd[0]; // it was already decided to let the result retire, so current retiring_pc must not be used as resume adress, as it will not match RF state
        assign current_exception_unit = exception_unit_table[retire_ids_next[0]];

        always_ff @(posedge clk) begin
            if (rst)
                branch_flush_r <= 0;
            else if (branch_flush) // when branch flush occured, all insns after the most recently retired one were invalid and must not be taken as resume address for interrupts
                branch_flush_r <= 1;
            else if (pc_id_assigned)
                branch_flush_r <= 0;
        end

     end else begin
        assign next_retiring_pc = '0;
        assign next_retiring_pc_invalid = 0;
        assign current_exception_unit = '0;
     end endgenerate

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    pc_id_assigned_without_pc_id_available_assertion:
        assert property (@(posedge clk) disable iff (rst) !(~pc_id_available & pc_id_assigned))
        else $error("ID assigned without any ID available");

    decode_advanced_without_id_assertion:
        assert property (@(posedge clk) disable iff (rst) !(~decode.valid & decode_advance))
        else $error("Decode advanced without ID");

endmodule
