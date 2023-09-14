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

module writeback

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    
    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter rf_params_t RF_CONFIG = get_derived_rf_params(CONFIG),
        parameter int unsigned NUM_WB_UNITS_PER_PORT [MAX_WB_GROUPS] = '{1, 4, 4},
        parameter int unsigned NUM_WB_UNITS = 9
    )

    (
        input logic clk,
        input logic rst,
        //Unit writeback
        unit_writeback_interface.wb unit_wb[NUM_WB_UNITS],
        //WB output
        output wb_packet_t wb_packet [RF_CONFIG.TOTAL_WB_GROUP_COUNT],
        //Snoop interface (LS unit)
        output wb_packet_t wb_snoop [RF_CONFIG.TOTAL_WB_GROUP_COUNT-1] // port0 writes immediately
    );

    //Writeback
    logic [NUM_WB_UNITS-1:0] unit_ack [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
    //aliases for write-back-interface signals
    id_t [NUM_WB_UNITS-1:0] unit_instruction_id [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
    logic [NUM_WB_UNITS-1:0] unit_done [RF_CONFIG.TOTAL_WB_GROUP_COUNT];

    typedef logic [MAX_POSSIBLE_REG_BITS-1:0] unit_rd_t [NUM_WB_UNITS];
    unit_rd_t unit_rd [RF_CONFIG.TOTAL_WB_GROUP_COUNT];
    //Per-ID muxes for commit buffer
    logic [$clog2(NUM_WB_UNITS)-1:0] unit_sel [RF_CONFIG.TOTAL_WB_GROUP_COUNT];

    typedef int unsigned unit_count_t [RF_CONFIG.TOTAL_WB_GROUP_COUNT];

    function static unit_count_t get_cumulative_unit_count();
        unit_count_t counts;
        int unsigned cumulative_count = 0;
        for (int i = 0; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin
            counts[i] = cumulative_count;
            cumulative_count += NUM_WB_UNITS_PER_PORT[i];
        end
        return counts;
    endfunction

    localparam unit_count_t CUMULATIVE_NUM_UNITS = get_cumulative_unit_count();

    genvar i, j;
    ////////////////////////////////////////////////////
    //Implementation
    //Re-assigning interface inputs to array types so that they can be dynamically indexed
    generate
        for (i = 0; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin : gen_wb_group_unpacking
            for (j = 0; j < NUM_WB_UNITS_PER_PORT[i]; j++) begin : gen_wb_unit_unpacking
                assign unit_instruction_id[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].id;
                assign unit_done[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].done;
                assign unit_wb[CUMULATIVE_NUM_UNITS[i] + j].ack = unit_ack[i][j];
            end
        end
    endgenerate

    //As units are selected for commit ports based on their unit ID,
    //for each additional commit port one unit can be skipped for the commit mux
    generate
        for (i = 0; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin : gen_wb_port_grouping
            for (j = 0; j < NUM_WB_UNITS_PER_PORT[i]; j++) begin : gen_wb_unit_grouping
                assign unit_rd[i][j] = unit_wb[CUMULATIVE_NUM_UNITS[i] + j].rd;
            end
        end
    endgenerate

    ////////////////////////////////////////////////////
    //Unit select for register file
    //Iterating through all commit ports:
    //   Search for complete units (in fixed unit order)
    //   Assign to a commit port, mask that unit and commit port
    generate for (i = 0; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin : gen_wb_mux
        priority_encoder
            #(.WIDTH(NUM_WB_UNITS_PER_PORT[i]))
        unit_done_encoder
        (
            .priority_vector (unit_done[i][NUM_WB_UNITS_PER_PORT[i]-1 : 0]),
            .encoded_result (unit_sel[i][NUM_WB_UNITS_PER_PORT[i] == 1 ? 0 : ($clog2(NUM_WB_UNITS_PER_PORT[i])-1) : 0])
        );
        assign wb_packet[i].valid = |unit_done[i];
        assign wb_packet [i].id = unit_instruction_id[i][unit_sel[i]];
        assign wb_packet[i].data = unit_rd[i][unit_sel[i]];

        assign unit_ack[i] = NUM_WB_UNITS'(wb_packet[i].valid) << unit_sel[i];
    end endgenerate

    ////////////////////////////////////////////////////
    //Store Forwarding Support
    //TODO: support additional writeback groups
    //currently limited to one writeback group with the
    //assumption that writeback group zero has single-cycle
    //operation
    always_ff @ (posedge clk) begin
        if (rst)
            for (int i=1; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++)
                wb_snoop[i-1].valid <= 0;
        else
            for (int i=1; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++)
                wb_snoop[i-1].valid <= wb_packet[i].valid;
    end
    always_ff @ (posedge clk) begin
        for (int i=1; i < RF_CONFIG.TOTAL_WB_GROUP_COUNT; i++) begin
            wb_snoop[i-1].data <= wb_packet[i].data; //TODO may need to be extended to commit-port 3 (fp) with 34b to forward float results to fsw too
            wb_snoop[i-1].id <= wb_packet[i].id;
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

endmodule
