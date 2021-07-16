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

    import taiga_config::*;
    import riscv_types::*;
    import taiga_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,

        input logic gc_init_clear,
        input logic gc_fetch_flush,

        //Fetch
        output id_t pc_id,
        output logic pc_id_available,
        input logic [31:0] if_pc,
        input logic pc_id_assigned,

        output id_t fetch_id,
        input logic early_branch_flush,
        input logic fetch_complete,
        input logic [31:0] fetch_instruction,
        input fetch_metadata_t fetch_metadata,

        //Decode ID
        output decode_packet_t decode,
        input logic decode_advance,
        input logic decode_uses_rd,
        input rs_addr_t decode_rd_addr,
        //renamer
        input phys_addr_t decode_phys_rd_addr,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued,
        input logic instruction_issued_with_rd,

        //WB
        input wb_packet_t wb_packet [CONFIG.NUM_WB_GROUPS],
        output commit_packet_t commit_packet [CONFIG.NUM_WB_GROUPS],

        //Retirer
        output retire_packet_t retire,
        output id_t retire_ids [RETIRE_PORTS],
        output logic retire_port_valid [RETIRE_PORTS],

        //CSR
        output logic [LOG2_MAX_IDS:0] post_issue_count,
        //Exception
        input id_t exception_id,
        output logic [31:0] exception_pc

    );
    //////////////////////////////////////////
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] pc_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [31:0] instruction_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] valid_fetch_addr_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) phys_addr_t phys_addr_table [MAX_IDS];
    (* ramstyle = "MLAB, no_rw_check" *) logic [0:0] uses_rd_table [MAX_IDS];

    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(fetch_metadata_t)-1:0] fetch_metadata_table [MAX_IDS];

    id_t decode_id;

    logic [LOG2_MAX_IDS:0] fetched_count;
    logic [LOG2_MAX_IDS:0] pre_issue_count;
    logic [LOG2_MAX_IDS:0] pre_issue_count_next;
    logic [LOG2_MAX_IDS:0] post_issue_count_next;
    logic [LOG2_MAX_IDS:0] inflight_count;

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
            uses_rd_table[decode_id] <= decode_uses_rd & |decode_rd_addr;
    end    
    ////////////////////////////////////////////////////
    //ID Management
    
    //Next ID always increases, except on a fetch buffer flush.
    //On a fetch buffer flush, the next ID is restored to the oldest non-issued ID (decode or issue stage)
    //This prevents a stall in the case where all  IDs are either in-flight or
    //in the fetch buffer at the point of a fetch flush.
    id_t oldest_pre_issue_id;
    id_t next_pc_id_base;
    id_t next_fetch_id_base;
    assign oldest_pre_issue_id = issue.stage_valid ? issue.id : decode_id;
    assign next_pc_id_base = gc_fetch_flush ? oldest_pre_issue_id : (early_branch_flush ? fetch_id : pc_id);
    assign next_fetch_id_base = gc_fetch_flush ? oldest_pre_issue_id : fetch_id;

    always_ff @ (posedge clk) begin
        if (rst) begin
            pc_id <= 0;
            fetch_id <= 0;
            decode_id <= 0;
        end
        else begin
            pc_id <= next_pc_id_base + LOG2_MAX_IDS'({pc_id_assigned & (~gc_fetch_flush)});
            fetch_id <= next_fetch_id_base + LOG2_MAX_IDS'({fetch_complete & ~gc_fetch_flush});
            decode_id <= ((gc_fetch_flush & issue.stage_valid) ? issue.id : decode_id) + LOG2_MAX_IDS'({decode_advance & ~gc_fetch_flush});
        end
    end
    //Retire IDs
    //Each retire port lags behind the previous one by one index (eg. [3, 2, 1, 0])
     generate for (i = 0; i < RETIRE_PORTS; i++) begin
        always_ff @ (posedge clk) begin
            if (rst)
                retire_ids[i] <= LOG2_MAX_IDS'(i);
            else
                retire_ids[i] <= retire_ids[i] + LOG2_MAX_IDS'(retire.count);
        end
    end endgenerate

    always_ff @ (posedge clk) begin
        if (rst | gc_fetch_flush)
            fetched_count <= 0;
        else
            fetched_count <= fetched_count + (LOG2_MAX_IDS+1)'(fetch_complete) - (LOG2_MAX_IDS+1)'(decode_advance);
    end

    assign pre_issue_count_next = pre_issue_count  + (LOG2_MAX_IDS+1)'(pc_id_assigned) - (LOG2_MAX_IDS+1)'(instruction_issued);
    always_ff @ (posedge clk) begin
        if (rst | gc_fetch_flush)
            pre_issue_count <= 0;
        else
            pre_issue_count <= pre_issue_count_next;
    end

    assign post_issue_count_next = post_issue_count  + (LOG2_MAX_IDS+1)'(instruction_issued) - (LOG2_MAX_IDS+1)'(retire.count);
    always_ff @ (posedge clk) begin
        if (rst)
            post_issue_count <= 0;
        else
            post_issue_count <= post_issue_count_next;
    end

    always_ff @ (posedge clk) begin
        if (rst)
            inflight_count <= 0;
        else
            inflight_count <= (gc_fetch_flush ? '0 : pre_issue_count_next) + post_issue_count_next;
    end

    ////////////////////////////////////////////////////
    //ID in-use determination
    logic id_inuse [RETIRE_PORTS];
    //WB group zero is not included as it completes within a single cycle
    //Non-writeback instructions not included as current instruction set
    //complete in their first cycle of the execute stage, or do not cause an
    //exception after that point
    toggle_memory_set # (
        .DEPTH (MAX_IDS),
        .NUM_WRITE_PORTS (2),
        .NUM_READ_PORTS (RETIRE_PORTS),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_inuse_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc_init_clear),
        .toggle ('{(instruction_issued_with_rd & issue.is_multicycle), wb_packet[1].valid}),
        .toggle_addr ('{issue.id, wb_packet[1].id}),
        .read_addr (retire_ids),
        .in_use (id_inuse)
    );

    ////////////////////////////////////////////////////
    //Retirer
    logic contiguous_retire;
    logic id_is_post_issue [RETIRE_PORTS];
    logic id_ready_to_retire [RETIRE_PORTS];
    logic [LOG2_RETIRE_PORTS-1:0] phys_id_sel;
    logic [RETIRE_PORTS-1:0] retire_id_uses_rd;
    logic [RETIRE_PORTS-1:0] retire_id_inuse;

     generate for (i = 0; i < RETIRE_PORTS; i++) begin
        assign retire_id_uses_rd[i] = uses_rd_table[retire_ids[i]];
        assign retire_id_inuse[i] = id_inuse[i];
     end endgenerate

    priority_encoder #(.WIDTH(RETIRE_PORTS))
    phys_id_sel_encoder (
        .priority_vector (retire_id_uses_rd & ~retire_id_inuse),
        .encoded_result (phys_id_sel)
    );
    assign retire.phys_id = retire_ids[phys_id_sel];

    always_comb begin
        contiguous_retire = 1;
        retire.valid = 0;
        retire.count = 0;
        //Supports retiring up to RETIRE_PORTS instructions.  The retired block of instructions must be
        //contiguous and must start with the first retire port.  Additionally, only one register file writing 
        //instruction is supported per cycle.
        for (int i = 0; i < RETIRE_PORTS; i++) begin
            id_is_post_issue[i] = post_issue_count > (LOG2_MAX_IDS+1)'(i);

            id_ready_to_retire[i] = (id_is_post_issue[i] & contiguous_retire & ~id_inuse[i]);
            retire_port_valid[i] = id_ready_to_retire[i] & ((~retire_id_uses_rd[i]) | (~retire.valid));

            contiguous_retire &= retire_port_valid[i];

            retire.valid |= retire_port_valid[i] & retire_id_uses_rd[i];
            retire.count += retire_port_valid[i];
        end
    end

    ////////////////////////////////////////////////////
    //Outputs
    assign pc_id_available = ~inflight_count[LOG2_MAX_IDS];

    //Decode
    assign decode.id = decode_id;
    assign decode.valid = |fetched_count;
    assign decode.pc = pc_table[decode_id];
    assign decode.instruction = instruction_table[decode_id];
    assign decode.fetch_metadata = fetch_metadata_table[decode_id];

    //Writeback/Commit support
    phys_addr_t commit_phys_addr [CONFIG.NUM_WB_GROUPS];
    assign commit_phys_addr[0] = issue.phys_rd_addr;
     generate for (i = 1; i < CONFIG.NUM_WB_GROUPS; i++) begin
        assign commit_phys_addr[i] = phys_addr_table[wb_packet[i].id];
     end endgenerate

     generate for (i = 0; i < CONFIG.NUM_WB_GROUPS; i++) begin
        assign commit_packet[i].id = wb_packet[i].id;
        assign commit_packet[i].phys_addr = commit_phys_addr[i];        
        assign commit_packet[i].valid = wb_packet[i].valid & |commit_phys_addr[i];
        assign commit_packet[i].data = wb_packet[i].data;
     end endgenerate

    //Exception Support
     generate if (CONFIG.INCLUDE_M_MODE) begin
         assign exception_pc = pc_table[exception_id];
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
