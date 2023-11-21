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

module renamer

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

        //Decode
        input logic decode_advance,
        renamer_interface.renamer decode,

        //Issue stage
        input issue_packet_t issue,
        input logic instruction_issued_with_rd,

        //Retire response
        input retire_packet_t retire
    );
    //////////////////////////////////////////
    typedef struct packed{
        rf_addr_t rd_addr;
        phys_addr_t spec_phys_addr;
        phys_addr_t previous_phys_addr;
        logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] previous_wb_group;
    } renamer_metadata_t;
    renamer_metadata_t inuse_list_input;
    renamer_metadata_t inuse_list_output;

    logic [5:0] clear_index;

    fifo_interface #(.DATA_WIDTH($bits(phys_addr_t))) free_list_gp ();
    fifo_interface #(.DATA_WIDTH($bits(phys_addr_t))) free_list_fp ();
    fifo_interface #(.DATA_WIDTH($bits(renamer_metadata_t))) inuse_list ();

    logic rename_valid_gp;
    logic rename_valid_fp;
    logic rollback_prerequisite, rollback_any, rollback_gp, rollback_fp;
    ////////////////////////////////////////////////////
    //Implementation
    //Assumption: MAX_IDS <= 32 thus, decode/rename stage can never stall due to lacking a free register
    //Zero register is never renamed
    //If a renamed destination is flushed in the issue stage, state is rolled back
    //When an instruction reaches the retire stage it either commits or reverts its renaming depending on whether the instruction retires or is discarded
    assign rename_valid_gp = (~gc.fetch_flush) & decode_advance & decode.uses_rd_gp & |decode.rd_addr;
    assign rename_valid_fp = (~gc.fetch_flush) & decode_advance & decode.uses_rd_fp;

    //Revert physcial address assignment on a flush
    assign rollback_prerequisite = gc.fetch_flush && issue.stage_valid && issue.uses_rd;
    assign rollback_any = rollback_prerequisite && |issue.rd_addr; // any rd_addr other than zero needs rollback, float addr have the isFloat bit in rd_addr set, so not 0
    assign rollback_gp = rollback_prerequisite && !issue.rd_addr.isFloat && |issue.rd_addr.rs;
    assign rollback_fp = rollback_prerequisite && issue.rd_addr.isFloat;

    //counter for indexing through memories for post-reset clearing/initialization
    lfsr #(.WIDTH(6), .NEEDS_RESET(0))
    lfsr_read_index (
        .clk (clk), .rst (rst),
        .en(gc.init_clear),
        .value(clear_index)
    );

    ////////////////////////////////////////////////////
    //Free list FIFO
    logic lastUsedFromFpFreeQueue;

    register_free_list #(.DATA_WIDTH($bits(phys_addr_t)), .FIFO_DEPTH(INFLIGHT_REG_WRITES_RESERVE)) free_list_fifo_gp (
        .clk (clk),
        .rst (rst),
        .fifo (free_list_gp),
        .rollback (rollback_gp)
    );

    //During post reset init, initialize FIFO with free list (registers 32-63)
    assign free_list_gp.potential_push = (gc.init_clear && ~clear_index[5]) || (retire.valid && !inuse_list_output.rd_addr.isFloat);
    assign free_list_gp.push = free_list_gp.potential_push;

    assign free_list_gp.data_in = gc.init_clear ? {1'b1, clear_index[4:0]} : (gc.writeback_suppress ? inuse_list_output.spec_phys_addr : inuse_list_output.previous_phys_addr);
    assign free_list_gp.pop = rename_valid_gp;


    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_fp_free_list
        register_free_list #(.DATA_WIDTH($bits(phys_addr_t)), .FIFO_DEPTH(INFLIGHT_REG_WRITES_RESERVE)) free_list_fifo_fp (
            .clk (clk),
            .rst (rst),
            .fifo (free_list_fp),
            .rollback (rollback_fp)
        );

        assign free_list_fp.potential_push = (gc.init_clear && ~clear_index[5]) || (retire.valid && inuse_list_output.rd_addr.isFloat);
        assign free_list_fp.push = free_list_fp.potential_push;

        assign free_list_fp.data_in = gc.init_clear ? {1'b1, clear_index[4:0]} : (gc.writeback_suppress ? inuse_list_output.spec_phys_addr : inuse_list_output.previous_phys_addr);
        assign free_list_fp.pop = rename_valid_fp;

    end endgenerate

    ////////////////////////////////////////////////////
    //Inuse list FIFO
    cva5_fifo #(.DATA_WIDTH($bits(renamer_metadata_t)), .FIFO_DEPTH(INFLIGHT_REG_WRITES_RESERVE)) inuse_list_fifo (
        .clk (clk),
        .rst (rst),
        .fifo (inuse_list)
    );

    assign inuse_list.potential_push = instruction_issued_with_rd & |issue.rd_addr;
    assign inuse_list.push = inuse_list.potential_push;

    assign inuse_list_input.rd_addr = issue.rd_addr;
    assign inuse_list_input.spec_phys_addr = issue.phys_rd_addr;
    assign inuse_list_input.previous_phys_addr = spec_table_previous_r.phys_addr;
    assign inuse_list_input.previous_wb_group = spec_table_previous_r.wb_group;
    assign inuse_list.data_in = inuse_list_input;

    assign inuse_list_output = inuse_list.data_out;
    assign inuse_list.pop = retire.valid;

    ////////////////////////////////////////////////////
    //Speculative rd-to-phys Table
    //On rollback restore the previous contents
    //During post reset init, initialize rd_to_phys with in-use list (lower 32 registers)
    typedef struct packed{
        phys_addr_t phys_addr; // fits 64 addresses, only within gp or fp. We differentiate both regFiles by using different RAMs, Tables and fifos (because different amount of wr+rd ports for each rf).
        logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] wb_group;
    } spec_table_t;
    rs_addr_t spec_tables_base_read_addr [GP_RF_FIXED_READ_PORT_COUNT+1]; // first 3 read_addrs are shared above both gp+fp (prev, rs1, rs2)
    spec_table_t spec_table_gp_read_data [GP_RF_FIXED_READ_PORT_COUNT+1];
    rs_addr_t spec_table_fp_rs3_read_addr; // rs3 only goes to the fp file
    spec_table_t spec_table_fp_read_data [FP_RF_FIXED_READ_PORT_COUNT+1];

    phys_addr_t spec_table_gp_phys_next_mux [4];
    phys_addr_t spec_table_gp_phys_next;
    logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] spec_tables_wb_group_next_mux [4];
    logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] spec_tables_wb_group_next;
    spec_table_t spec_table_gp_previous, spec_table_fp_previous;
    spec_table_t spec_table_previous_r;

    logic spec_table_gp_update, spec_table_fp_update;
    rs_addr_t spec_tables_write_index;
    rs_addr_t spec_tables_write_index_mux [4];

    logic already_restored_current_gp, already_restored_current_fp;

    assign spec_table_gp_update = rollback_gp || rename_valid_gp || gc.init_clear || (retire.valid && gc.writeback_suppress && !inuse_list_output.rd_addr.isFloat && !already_restored_current_gp);
    assign spec_table_fp_update = rollback_fp || rename_valid_fp || gc.init_clear || (retire.valid && gc.writeback_suppress && inuse_list_output.rd_addr.isFloat && !already_restored_current_fp);

    logic [1:0] spec_tables_sel;
    
    one_hot_to_integer #(.C_WIDTH(4)) spec_table_sel_one_hot_to_int (
        .one_hot ({gc.init_clear, rollback_any, (retire.valid && gc.writeback_suppress), 1'b0}),
        .int_out (spec_tables_sel)
    );

    //Normal operation
    assign spec_tables_write_index_mux[0] = decode.rd_addr;
    assign spec_table_gp_phys_next_mux[0] = free_list_gp.data_out;
    assign spec_tables_wb_group_next_mux[0] = decode.rd_wb_group;
    //gc.writeback_suppress
    assign spec_tables_write_index_mux[1] = inuse_list_output.rd_addr.rs;
    assign spec_table_gp_phys_next_mux[1] = inuse_list_output.previous_phys_addr;
    assign spec_tables_wb_group_next_mux[1] = inuse_list_output.previous_wb_group;
    //rollback
    assign spec_tables_write_index_mux[2] = issue.rd_addr.rs;
    assign spec_table_gp_phys_next_mux[2] = spec_table_previous_r.phys_addr;
    assign spec_tables_wb_group_next_mux[2] = spec_table_previous_r.wb_group;
    //gc.init_clear
    assign spec_tables_write_index_mux[3] = clear_index[4:0];
    assign spec_table_gp_phys_next_mux[3] = {1'b0, clear_index[4:0]};
    assign spec_tables_wb_group_next_mux[3] = '0;

    assign spec_tables_write_index = spec_tables_write_index_mux[spec_tables_sel];
    assign spec_table_gp_phys_next = spec_table_gp_phys_next_mux[spec_tables_sel];
    assign spec_tables_wb_group_next = spec_tables_wb_group_next_mux[spec_tables_sel];

    assign spec_tables_base_read_addr[0] = spec_tables_write_index;
    assign spec_tables_base_read_addr[1:2] = '{decode.rs_addr[RS1].rs, decode.rs_addr[RS2].rs};

    lutram_1w_mr #(
        .WIDTH($bits(spec_table_t)),
        .DEPTH(32),
        .NUM_READ_PORTS(2+1) // 1 (prev) + 2 gp read ports
    )
    spec_table_gp_ram (
        .clk(clk),
        .waddr(spec_tables_write_index),
        .raddr(spec_tables_base_read_addr),
        .ram_write(spec_table_gp_update),
        .new_ram_data({spec_table_gp_phys_next, spec_tables_wb_group_next}),
        .ram_data_out(spec_table_gp_read_data)
    );
    assign spec_table_gp_previous = spec_table_gp_read_data[0];

    // Issue: if left alone, writeback_suppress might restore the same ISA reg's mapping twice
    //    lui  a1,0x33333     <- overwrites original mapping of a1
    //    addi a1, a1, 0x333  <- overwrites new mapping of a1 again
    // with both being speculative, already issued and needing to be reverted.
    // Since the restoration is in execution order, the newer states are wrong when we want the original state back => need to prevent only the first writeback_suppress per ISA reg to be restore to spec_table
    // this is the simplest solution I could come up with.
    // Alternatives:
    //    * store up to [INFLIGHT] ISA regAddr and compare each suppressed one with the already valid ones. Requires reset of up to [INFLIGHT] valid bits and comparisons on fetch_flush, but stores 7*[INFLIGHT] bits
    //    * Track which mappings are inflight (might also have debugging purposes). But difficult, because in the exact situation, the same mapping, say a1 can be in flight multiple times with multiple phys-regs as destinations.
    //      we would neeed to keep track of how many are still in flight per ISA reg, so that we could prevent all but the oldest be restored. So more than just a toggle-set. What is the upper limit of the same reg in flight? [INFLIGHT]?
    //      its dead code, unless there are dependencies, but then they wont be inflight at the same time (unless sw)
    //    * overhaul GC significantly. This seems to affect interrupts the most, and there, there is room for interpretation of which instruction will be the interrupted one and which will go through. It is not actually needed to suppress inflight results, we could just interrupt a later instruction
    //      but I do not see why this issue could not affect branches in the same way under the right circumstances. And changing GC was hard the first time, as it needs to be in-sync with a lot of distributed state without the state to sync with being directly available

    logic restore_mapping_state_gp [0:31];

    always_ff @(posedge clk) begin
        if (rst || gc.fetch_flush) begin
            for (int i=0; i < 32; i++)
                restore_mapping_state_gp[i] <= 0;
        end else if (retire.valid && gc.writeback_suppress && !inuse_list_output.rd_addr.isFloat) begin
            restore_mapping_state_gp[inuse_list_output.rd_addr.rs] <= 1;
        end
    end

    assign already_restored_current_gp = restore_mapping_state_gp[inuse_list_output.rd_addr.rs];





    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_fp_spec_tab

        phys_addr_t spec_table_fp_phys_next_mux [4];
        phys_addr_t spec_table_fp_phys_next;

        //Normal operation
        assign spec_table_fp_phys_next_mux[0] = free_list_fp.data_out;
        //gc.writeback_suppress
        assign spec_table_fp_phys_next_mux[1] = inuse_list_output.previous_phys_addr;
        //rollback
        assign spec_table_fp_phys_next_mux[2] = spec_table_previous_r.phys_addr;
        //gc.init_clear
        assign spec_table_fp_phys_next_mux[3] = {1'b0, clear_index[4:0]};

        assign spec_table_fp_phys_next = spec_table_fp_phys_next_mux[spec_tables_sel];

        assign spec_table_fp_rs3_read_addr = decode.rs_addr[RS3].rs;

        lutram_1w_mr #(
            .WIDTH($bits(spec_table_t)),
            .DEPTH(32),
            .NUM_READ_PORTS(3+1) // 1 (prev) + 3 fp read ports
        )
        spec_table_fp_ram (
            .clk(clk),
            .waddr(spec_tables_write_index),
            .raddr('{
                spec_tables_base_read_addr[0],
                spec_tables_base_read_addr[1],
                spec_tables_base_read_addr[2],
                spec_table_fp_rs3_read_addr
            }),
            .ram_write(spec_table_fp_update),
            .new_ram_data({spec_table_fp_phys_next, spec_tables_wb_group_next}),
            .ram_data_out(spec_table_fp_read_data)
        );
        assign spec_table_fp_previous = spec_table_fp_read_data[0];

        always_ff @ (posedge clk) begin
            if (spec_table_fp_update || spec_table_gp_update) begin
                spec_table_previous_r <= (spec_table_fp_update)? spec_table_fp_previous : spec_table_gp_previous;
            end
        end


        // same as for GP, although probably even more rare outside of useless code (overwriting the same reg again and again without using the result)
        // FP has no useful 0-cycle pipe like the IALU, so multiple useful instructions being speculated will be RARE. But it will still brake the micro-arch-state
        logic restore_mapping_state_fp [0:31];

        always_ff @(posedge clk) begin
            if (rst || gc.fetch_flush) begin
                for (int i=0; i < 32; i++)
                    restore_mapping_state_fp[i] <= 0;
            end else if (retire.valid && gc.writeback_suppress && inuse_list_output.rd_addr.isFloat) begin
                restore_mapping_state_fp[inuse_list_output.rd_addr.rs] <= 1;
            end
        end

        assign already_restored_current_fp = restore_mapping_state_fp[inuse_list_output.rd_addr.rs];
    end else begin 
        always_ff @ (posedge clk) begin
            if (spec_table_gp_update) begin
                spec_table_previous_r <= spec_table_gp_previous;
            end
        end
        assign already_restored_current_fp = 0;
    end endgenerate
    

    ////////////////////////////////////////////////////
    //Renamed Outputs
    spec_table_t [RF_CONFIG.TOTAL_READ_PORT_COUNT-1:0] spec_table_decode;
    generate for (genvar i = 0; i < RF_CONFIG.TOTAL_READ_PORT_COUNT; i++) begin : gen_renamed_addrs
        if (i < GP_RF_FIXED_READ_PORT_COUNT) begin
            assign spec_table_decode[i] = spec_table_gp_read_data[i+1];
        end else begin
            assign spec_table_decode[i] = spec_table_fp_read_data[i-GP_RF_FIXED_READ_PORT_COUNT+1];
        end

        assign decode.phys_rs_addr[i] = spec_table_decode[i].phys_addr;
        assign decode.rs_wb_group[i] = spec_table_decode[i].wb_group;
    end endgenerate

    assign decode.phys_rd_addr = decode.uses_rd_fp? free_list_fp.data_out : (|decode.rd_addr ? free_list_gp.data_out : '0);
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions
    rename_rd_zero_assertion:
        assert property (@(posedge clk) disable iff (rst) (decode.uses_rd_gp && decode.rd_addr == 0) |-> (decode.phys_rd_addr == 0)) else $error("rd zero renamed");

    for (genvar i = 0; i < GP_RF_FIXED_READ_PORT_COUNT; i++) begin : rename_rs_zero_assertion
        assert property (@(posedge clk) disable iff (rst) (decode.rs_addr[i] == 0) |-> (decode.phys_rs_addr[i] == 0)) else $error("rs zero renamed");
    end

endmodule
