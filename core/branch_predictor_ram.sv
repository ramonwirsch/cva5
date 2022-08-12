/*
 * Copyright © 2019 Eric Matthews,  Lesley Shannon
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

module branch_predictor_ram

    import cva5_config::*;
    import cva5_types::*;

    #(
        parameter C_DATA_WIDTH = 20,
        parameter C_DEPTH = 512
    )
    (
       // Global signals
        input logic clk,
        input logic rst,

        // Port A (read only)
        input logic read_en_a,
        input logic[$clog2(C_DEPTH)-1:0] read_addr_a,
        output logic[C_DATA_WIDTH-1:0] read_data_a,

        // Port B (read and write)
        input logic en_b,
        input logic we_b,
        input logic[$clog2(C_DEPTH)-1:0] addr_b,
        input logic[C_DATA_WIDTH-1:0] data_in_b,
        output logic[C_DATA_WIDTH-1:0] data_out_b
    );

    // internal wires for B write to A read bypass
    logic[C_DATA_WIDTH-1:0] out_a;

    // internal regs for B write to A read bypass
    logic simultaneous_access_r;
    logic[$clog2(C_DEPTH)-1:0] read_addr_a_r;
    logic[$clog2(C_DEPTH)-1:0] addr_b_r;
    logic[C_DATA_WIDTH-1:0] data_bypass_b_r;

    //implementation
    ////////////////////////////////////////////////////

    //Branch Predictors Write first RAM needed to handle the following potential collision:
    //An update from a miss occurs on the same cycle as a subsequent fetch to the same instruction

    //enable bypass in case of a write to the same address as port A reads from. (done this way to break critical path in addr-match calculation path).
    assign read_data_a = simultaneous_access_r && (read_addr_a_r == addr_b_r) ? data_bypass_b_r : out_a;

    //store info for bypass from port B to port A in registers to be used in next clock cycle if needed.
    always_ff @(posedge clk) begin
        simultaneous_access_r <= we_b & read_en_a;
        read_addr_a_r <= read_addr_a;
        addr_b_r <= addr_b;
        data_bypass_b_r <= data_in_b;
    end

    // inferred ram implementation (true-dual-ported in write first mode)
    // channel a is used for reading only, channel b has read and write capabilities
    xilinx_tdp_ram_wf#(
        .C_DATA_WIDTH(C_DATA_WIDTH),
        .C_DEPTH(C_DEPTH)
    ) branch_ram (
        .clk(clk),

        .en_a(read_en_a),
        .we_a(0), // port A read only
        .addr_a(read_addr_a),
        .data_in_a('0),
        .data_out_a(out_a),

        .en_b(en_b),
        .we_b(we_b),
        .addr_b(addr_b),
        .data_in_b(data_in_b),
        .data_out_b(data_out_b)
    );

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface

endmodule
