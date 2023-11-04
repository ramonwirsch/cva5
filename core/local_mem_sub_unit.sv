/*
 * Copyright © 2017 Eric Matthews,  Lesley Shannon
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

module local_mem_sub_unit

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter INCLUDE_AMO = 0
    )

    (
        input logic clk,
        input logic rst,

        memory_sub_unit_interface.responder unit,
        local_memory_interface.master local_mem,
        input amo_details_t amo
    );

    
    logic [XLEN-3:0] word_addr;
    assign word_addr = unit.addr[31:2];

    amo_alu_inputs_t amo_alu_inputs;
    logic [XLEN-1:0] amo_rs2;
    logic amo_read_modify_write_in_progress;
    logic [XLEN-3:0] amo_addr;

    assign amo_alu_inputs.rs1_load = local_mem.data_out;
    assign amo_alu_inputs.rs2 = amo_rs2;
    assign amo_alu_inputs.op = amo.op;

    ////////////////////////////////////////////////////
    //AMO logic (Compiler can only support AMO for all addresses or none. So to not silently drop the modifications of ops like amoadd when they are going to local memory, those ops still need to be applied heredecoder does not )
    //             (decoder has no microcode support and does not handle selecting memory sub units in order to replace amoadd with lw add there)
    //             (lr, sc are ignored / handled like normal reads and writes. TODO we should reserve addresses in case there are multiple threads that use that instead of locking the scheduler)
    generate if (INCLUDE_AMO) begin: gen_amo
        logic [XLEN-1:0] amo_result;
        logic amo_read_then_write;
        assign amo_read_then_write = unit.new_request && amo.is_rmw && amo.op != AMO_SWAP_FN5;

        always_ff @ (posedge clk) begin
            amo_rs2 <= unit.data_in;
            amo_addr <= word_addr;
            if (rst)
                amo_read_modify_write_in_progress <= 0;
            else if (amo_read_modify_write_in_progress)
                amo_read_modify_write_in_progress <= 0;
            else
                amo_read_modify_write_in_progress <= amo_read_then_write; // on for 1 cycle, if we do any read-mody-write op

        end

        amo_alu amo_unit (
            .amo_alu_inputs (amo_alu_inputs), 
            .result (amo_result)
        );

        assign local_mem.data_in = amo_read_modify_write_in_progress? amo_result : unit.data_in;
        assign local_mem.en = unit.new_request || amo_read_modify_write_in_progress;
        assign local_mem.be = amo_read_modify_write_in_progress? 4'hF : (amo_read_then_write? 4'h0 : unit.be);

    end else begin
        assign local_mem.data_in = unit.data_in;
        assign local_mem.en = unit.new_request;
        assign local_mem.be = unit.be;
        assign amo_read_modify_write_in_progress = 0;
    end endgenerate

    assign local_mem.addr = amo_read_modify_write_in_progress? amo_addr : word_addr;
    assign unit.data_out = local_mem.data_out;
    assign unit.ready = !amo_read_modify_write_in_progress;

    always_ff @ (posedge clk) begin
        if (rst)
            unit.data_valid <= 0;
        else
            unit.data_valid <= unit.new_request && (unit.re || amo.is_rmw);
    end

endmodule
