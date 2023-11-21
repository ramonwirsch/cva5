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

 `define max(a,b) ((a > b) ? a : b)

module register_file

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    # (
        parameter WRITE_PORTS = 2,
        parameter READ_PORTS = 2,
        parameter DATA_WIDTH = 32,
        parameter DEPTH = 64,
        parameter SELF_FLUSH = 0 // GP_RF flushed on write_port 1, which is ALU. Because the rf_issue.phys_rd addr is always the one to flush & the one for alu-single-issue writebacks
    ) // FP_RF cannot do that, because there is no single-issue write-port. Need to multiplex flushing on write_port 0 (because flushing procludes marking new reg as inflight, but fpu writebacks might still occur)
    // "rf_issue.single_cycle_or_flush" just means flush in that case
    (
        input logic clk,
        input logic rst,
        input gc_outputs_t gc,

        //decode write interface
        input phys_addr_t decode_phys_rs_addr [READ_PORTS],
        input logic [`max($clog2(WRITE_PORTS)-1, 0):0] decode_rs_wb_group [READ_PORTS],
        input phys_addr_t decode_phys_rd_addr,
        input logic decode_advance,
        input logic decode_uses_rd,

        // infligh_writes
        input phys_addr_t inflight_commit_addr_per_port [WRITE_PORTS], // so that parent can override which source to use to signal writing (done for GP seemingly to shorten path for alu-port/commit0)
        input logic inflight_commit_per_port [WRITE_PORTS], // so that parent can override which source to use

        //Issue interface
        register_file_issue_interface.register_file rf_issue,

        //Writeback
        input commit_packet_t commit [WRITE_PORTS]
    );
    typedef logic [DATA_WIDTH-1:0] rs_data_set_t [READ_PORTS];
    rs_data_set_t rs_data_set [WRITE_PORTS];

    logic decode_inuse [READ_PORTS];
    logic decode_inuse_r [READ_PORTS];

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation

    ////////////////////////////////////////////////////
    //Phys register inuse
    // Example for GP-RF:
    //toggle ports: decode advance, single-cycle/fetch_flush, multi-cycle commit
    //read ports: rs-decode, rs-issue

    logic inflight_notify [1+WRITE_PORTS];
    phys_addr_t inflight_notify_addr [1+WRITE_PORTS];
    phys_addr_t inflight_check_addr [READ_PORTS*2];
    logic inflight_check_result [READ_PORTS*2];

    generate if (SELF_FLUSH) begin : gen_self_flush
        assign inflight_notify[0] = (decode_advance && decode_uses_rd && ~gc.fetch_flush) || rf_issue.single_cycle_or_flush;
        assign inflight_notify_addr[0] = rf_issue.single_cycle_or_flush? rf_issue.phys_rd_addr : decode_phys_rd_addr;
    end else begin
        assign inflight_notify[0] = (decode_advance & decode_uses_rd & ~gc.fetch_flush);
        assign inflight_notify_addr[0] = decode_phys_rd_addr;
    end endgenerate

    generate for (i = 0; i < READ_PORTS; i++) begin : gen_in_flight_vectors
        assign inflight_check_addr[i] = decode_phys_rs_addr[i];
        assign inflight_check_addr[READ_PORTS+i] = rf_issue.phys_rs_addr[i];

        assign decode_inuse[i] = inflight_check_result[i];
        assign rf_issue.inuse[i] = inflight_check_result[READ_PORTS+i];
    end endgenerate

    toggle_memory_set # (
        .DEPTH (DEPTH),
        .NUM_WRITE_PORTS (1 + WRITE_PORTS),
        .NUM_READ_PORTS (READ_PORTS*2),
        .WRITE_INDEX_FOR_RESET (0),
        .READ_INDEX_FOR_RESET (0)
    ) id_inuse_toggle_mem_set
    (
        .clk (clk),
        .rst (rst),
        .init_clear (gc.init_clear),
        .toggle (inflight_notify), // first is always the decoded dest reg to declare a reg "inflight". Then one for each commit-port to declare completion if actually written
        .toggle_addr (inflight_notify_addr), // addresses match above
        .read_addr (inflight_check_addr), // first half is decode_rs addrs. Second half is just issued addresses
        .in_use (inflight_check_result) // results of inflight check above (first half for addresses in decode / requesting read, second half for addresses just issued)
    );

    always_ff @ (posedge clk) begin
        if (decode_advance)
            decode_inuse_r <= decode_inuse;
    end

    ////////////////////////////////////////////////////
    //Register Banks
    //Implemented in seperate module as there is not universal tool support for inferring
    //arrays of memory blocks.
    generate for (i = 0; i < WRITE_PORTS; i++) begin : gen_reg_banks
        assign inflight_notify[1+i] = inflight_commit_per_port[i];
        assign inflight_notify_addr[1+i] = inflight_commit_addr_per_port[i];

        register_bank #(
            .NUM_READ_PORTS(READ_PORTS),
            .DATA_WIDTH(DATA_WIDTH),
            .DEPTH(DEPTH)
        ) reg_group (
            .clk(clk),
            .rst(rst),
            .write_addr(commit[i].phys_addr),
            .new_data(commit[i].data[DATA_WIDTH-1:0]),
            .commit(commit[i].valid & ~gc.writeback_suppress),
            .read_addr(decode_phys_rs_addr),
            .data(rs_data_set[i])
        );
    end endgenerate

    ////////////////////////////////////////////////////
    //Register File Muxing
    logic [`max($clog2(WRITE_PORTS)-1, 0):0] rs_wb_group [READ_PORTS];
    logic bypass [READ_PORTS];
    assign rs_wb_group = decode_advance ? decode_rs_wb_group : rf_issue.rs_wb_group;
    assign bypass = decode_advance ? decode_inuse : decode_inuse_r;

    always_ff @ (posedge clk) begin
       for (int i = 0; i < READ_PORTS; i++) begin
           if (decode_advance | rf_issue.inuse[i])
               rf_issue.data[i][DATA_WIDTH-1:0] <= bypass[i] ? commit[rs_wb_group[i]].data[DATA_WIDTH-1:0] : rs_data_set[rs_wb_group[i]][i];
       end
   end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    //for (genvar i = 0; i < WRITE_PORTS; i++) begin : write_to_rd_zero_assertion
    //    assert property (@(posedge clk) disable iff (rst) (commit[i].valid) |-> (commit[i].phys_addr != 0)) else $error("write to register zero");
    //end

endmodule
