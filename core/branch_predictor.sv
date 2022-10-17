/*
 * Copyright © 2017-2020 Eric Matthews,  Lesley Shannon
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

module branch_predictor

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG
    )

    (
        input logic clk,
        input logic rst,
        branch_predictor_interface.branch_predictor bp,
        input branch_results_t br_results,
        ras_interface.branch_predictor ras,

        instruction_invalidation_queued.sink instr_inv
    );

    //BP tag width can be reduced, based on memory size, when virtual address
    //support is not enabled

    localparam longint CACHE_MIN = (CONFIG.INCLUDE_ICACHE) ? 64'(CONFIG.ICACHE_ADDR.L) : 64'h00000000FFFFFFFF;
    localparam longint BUS_MIN = (CONFIG.INCLUDE_IBUS) ? 64'(CONFIG.IBUS_ADDR.L) : 64'h00000000FFFFFFFF;
    localparam longint LOCAL_MIN = (CONFIG.INCLUDE_ILOCAL_MEM) ? 64'(CONFIG.ILOCAL_MEM_ADDR.L) : 64'h00000000FFFFFFFF;

    localparam longint CACHE_MAX = (CONFIG.INCLUDE_ICACHE) ? 64'(CONFIG.ICACHE_ADDR.H) : 64'h0;
    localparam longint BUS_MAX = (CONFIG.INCLUDE_IBUS) ? 64'(CONFIG.IBUS_ADDR.H) : 64'h0;
    localparam longint LOCAL_MAX = (CONFIG.INCLUDE_ILOCAL_MEM) ? 64'(CONFIG.ILOCAL_MEM_ADDR.H) : 64'h0;

    `define max(a,b) ((a > b) ? a : b)
    `define min(a,b) ((a < b) ? a : b)

    localparam longint RANGE_MIN = `min(CACHE_MIN, `min(BUS_MIN, LOCAL_MIN));
    localparam longint RANGE_MAX = `max(CACHE_MAX, `max(BUS_MAX, LOCAL_MAX));


    function int get_memory_width();
        if(CONFIG.INCLUDE_S_MODE)
            return 32;
        else begin
            return $clog2(RANGE_MAX);
        end
    endfunction : get_memory_width

    localparam BRANCH_ADDR_W = $clog2(CONFIG.BP.ENTRIES);
    localparam BTAG_W = get_memory_width() - BRANCH_ADDR_W - 2;

    function logic[BTAG_W-1:0] get_tag (input logic[31:0] pc);
        return pc[BRANCH_ADDR_W+2 +: BTAG_W];
    endfunction

    typedef struct packed {
        logic valid;
        logic [BTAG_W-1:0] tag;
        logic is_branch;
        logic is_return;
        logic is_call;
        branch_predictor_metadata_t metadata;
    } branch_table_entry_t;

    branch_table_entry_t [CONFIG.BP.WAYS-1:0] if_entry;
    branch_table_entry_t ex_entry;
    branch_table_entry_t [CONFIG.BP.WAYS-1:0] tag_write_data;
    branch_table_entry_t [CONFIG.BP.WAYS-1:0] tag_maybe_to_invalidate;

    typedef struct packed{
        branch_predictor_metadata_t branch_predictor_metadata;
        logic branch_prediction_used;
        logic [CONFIG.BP.WAYS-1:0] branch_predictor_update_way;
    } branch_metadata_t;
    (* ramstyle = "MLAB, no_rw_check" *) logic [$bits(branch_metadata_t)-1:0] branch_metadata_table [MAX_IDS];
    branch_metadata_t branch_metadata_if;
    branch_metadata_t branch_metadata_ex;

    logic branch_predictor_direction_changed;
    logic [CONFIG.BP.WAYS-1:0][31:0] target_write_data;
    logic [CONFIG.BP.WAYS-1:0][31:0] predicted_pc;

    logic [CONFIG.BP.WAYS-1:0] tag_matches; // Matches with looked-for tag on Bank Port A
    logic [CONFIG.BP.WAYS-1:0] inv_tag_matches; // Matches with invaliation on Bank Port B
    logic [CONFIG.BP.WAYS-1:0] replacement_way;
    logic [CONFIG.BP.WAYS-1:0] observation_update_now; // banks we need to write the observation update to currently (remembered from incoming br_result)
    logic [CONFIG.BP.WAYS-1:0] inv_way_now; // do we need invalidation in the current cycle
    logic [CONFIG.BP.WAYS-1:0] inv_way_needed_stalled; // register, stores latest inv_needed, in case observation_update superseeds us
    logic [CONFIG.BP.WAYS-1:0] tag_write_way; // result of invalidation and observation_update, which banks will get written to this cycle
    logic [CONFIG.BP.WAYS-1:0] target_write_way; // same as tag_update_way for the dest-addr banks
    logic [$clog2(CONFIG.BP.WAYS > 1 ? CONFIG.BP.WAYS : 2)-1:0] hit_way;
    logic tag_match;
    logic use_predicted_pc;

    // incoming update by observing control-flow
    logic observation_update;
    // we have an ongoing invalidation (no matter which state)
    logic inv_pending;

    logic miss_or_invalidate;

    // internal address to update
    logic [BRANCH_ADDR_W-1:0] observation_update_baddr;
    logic [BRANCH_ADDR_W-1:0] inv_baddr;
    logic [CONFIG.BP.WAYS-1:0][BRANCH_ADDR_W-1:0] update_internal_addr;


    /////////////////////////////////////////
    // we have received a new observation that we will save
    assign observation_update = br_results.valid;
    // we have received an addr to invalidate in all Ways
    assign inv_pending = CONFIG.INSTRUCTION_COHERENCY & instr_inv.inv_valid;
    
    generate if (CONFIG.INSTRUCTION_COHERENCY) begin : gen_insn_inv

        // tracks wether we completed the look or not
        logic [1:0] inv_progress;
        // invalidation was given to banks, will be written next cycle
        logic inv_write_can_complete;

        assign inv_write_can_complete = (inv_way_now & ~observation_update_now) == inv_way_now; // all wanted invalidations are possible this cycle
    
        assign instr_inv.inv_completed = inv_progress != '0 & inv_write_can_complete; // we are writing all remaining invalidations to banks this cycle (after we checked for banks to invalidate)

        always_ff @(posedge clk) begin
            if (rst) begin
                inv_progress <= 0;
            end else if (inv_pending & inv_progress == 0) begin
                if (~observation_update) begin // lookup is uninterrupted, will know inv_tag_matches next cycle
                    inv_progress <= 1;
                end
            end else if (inv_progress == 1) begin
                if (inv_write_can_complete) begin // can consume next inv_instr next cycle
                    inv_progress <= 0;
                end else begin // superseded by obs_update, remember what to invalidate
                    inv_way_needed_stalled <= inv_tag_matches;
                    inv_progress <= 2;
                end
            end else if (inv_progress == 2) begin
                if (inv_write_can_complete) begin
                    inv_progress <= 0;
                end
            end
        end

        assign inv_way_now = (inv_progress == 0)? '0 : ((inv_progress == 2)? inv_way_needed_stalled : inv_tag_matches);
    end else begin
        assign instr_inv.inv_completed = 0;
    end
    endgenerate

    /////////////////////////////////////////
    // muxing of branch updates and invalidation logic
    assign miss_or_invalidate = observation_update | inv_pending;
    assign observation_update_baddr = br_results.pc[2 +: BRANCH_ADDR_W];
    assign inv_baddr = instr_inv.inv_addr[2 +: BRANCH_ADDR_W];

    genvar i;
    generate if (CONFIG.INCLUDE_BRANCH_PREDICTOR)
    for (i=0; i<CONFIG.BP.WAYS; i++) begin : gen_branch_tag_banks // kept org name, so that waveforms match better with previous results
        assign tag_write_data[i] = observation_update_now[i] ?
                    ex_entry :
                    '{default: 0};

        assign target_write_data[i] = observation_update_now[i] ?
                    br_results.target_pc :
                    0; // jump addr to 0, this will result in an assertion if used accidencially!

        assign update_internal_addr[i] = observation_update_now[i] ?  // update either due to observation update or invalidation, we can do both if different banks
                    observation_update_baddr :
                    inv_baddr;

        branch_predictor_ram #(.C_DATA_WIDTH($bits(branch_table_entry_t)), .C_DEPTH(CONFIG.BP.ENTRIES))
        tag_bank (       
            .clk            (clk),
            .rst            (rst),

            .read_addr_a    (bp.next_pc[2 +: BRANCH_ADDR_W]),  // PortA used to check for predictions / get predictions
            .read_en_a      (bp.new_mem_request), 
            .read_data_a    (if_entry[i]),

            .en_b           (miss_or_invalidate), // PortB used to look for data that has to be invalidated & storing observations (storing has priority)
            .addr_b         (update_internal_addr[i]), 
            .we_b           (tag_write_way[i]), 
            .data_in_b      (tag_write_data[i]),
            .data_out_b     (tag_maybe_to_invalidate[i]) // when not writing, this is the current tag. Used to check for matches with data to invalidate
        );
    
        branch_predictor_ram #(.C_DATA_WIDTH(32), .C_DEPTH(CONFIG.BP.ENTRIES))
        addr_table (       
            .clk            (clk),
            .rst            (rst),

            .read_addr_a    (bp.next_pc[2 +: BRANCH_ADDR_W]),  // PortA used to check for predictions / get predictions
            .read_en_a      (bp.new_mem_request), 
            .read_data_a    (predicted_pc[i]),

            .en_b           (miss_or_invalidate), // PortB used to store observations
            .addr_b         (update_internal_addr[i]), 
            .we_b           (target_write_way[i]), 
            .data_in_b      (target_write_data[i]),
            .data_out_b     (/*unused*/)
        );
    end
    endgenerate

    generate if (CONFIG.INCLUDE_BRANCH_PREDICTOR)
    for (i=0; i<CONFIG.BP.WAYS; i++) begin : gen_branch_hit_detection
            assign tag_matches[i] = ({if_entry[i].valid, if_entry[i].tag} == {1'b1, get_tag(bp.if_pc)});
            assign inv_tag_matches[i] = tag_maybe_to_invalidate[i].valid & (tag_maybe_to_invalidate[i].tag == get_tag({instr_inv.inv_addr, 2'b00}));
    end
    endgenerate

    ////////////////////////////////////////////////////
    //Instruction Fetch Response
    generate if (CONFIG.BP.WAYS > 1)
        one_hot_to_integer #(CONFIG.BP.WAYS)
        hit_way_conv (       
            .one_hot(tag_matches), 
            .int_out(hit_way)
        );
    else
        assign hit_way = 0;
    endgenerate
    assign tag_match = |tag_matches;

    assign use_predicted_pc = CONFIG.INCLUDE_BRANCH_PREDICTOR & tag_match;

    //Predicted PC and whether the prediction is valid
    assign bp.predicted_pc = predicted_pc[hit_way];
    assign bp.use_prediction = use_predicted_pc;
    assign bp.is_branch = if_entry[hit_way].is_branch;
    assign bp.is_return = if_entry[hit_way].is_return;
    assign bp.is_call = if_entry[hit_way].is_call;

    ////////////////////////////////////////////////////
    //Instruction Fetch metadata
    cycler #(CONFIG.BP.WAYS)
    replacement_policy (       
        .clk (clk),
        .rst (rst), 
        .en (1'b1), 
        .one_hot (replacement_way)
    );
    assign branch_metadata_if.branch_predictor_metadata = if_entry[hit_way].metadata;
    assign branch_metadata_if.branch_prediction_used = use_predicted_pc;
    assign branch_metadata_if.branch_predictor_update_way = tag_match ? tag_matches : replacement_way;

    always_ff @ (posedge clk) begin
        if (bp.pc_id_assigned)
            branch_metadata_table[bp.pc_id] <= branch_metadata_if;
    end
    assign branch_metadata_ex = branch_metadata_table[br_results.id];

    ////////////////////////////////////////////////////
    //Execution stage update
    assign ex_entry.valid = 1;
    assign ex_entry.tag = get_tag(br_results.pc);
    assign ex_entry.is_branch = br_results.is_branch;
    assign ex_entry.is_return = br_results.is_return;
    assign ex_entry.is_call = br_results.is_call;


    //2-bit saturating counter
    always_comb begin
        case(branch_metadata_ex.branch_predictor_metadata)
            2'b00 : ex_entry.metadata = br_results.branch_taken ? 2'b01 : 2'b00;
            2'b01 : ex_entry.metadata = br_results.branch_taken ? 2'b10 : 2'b00;
            2'b10 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b01;
            2'b11 : ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b10;
        endcase
        if (~branch_metadata_ex.branch_prediction_used)
            ex_entry.metadata = br_results.branch_taken ? 2'b11 : 2'b00;
    end
    assign branch_predictor_direction_changed =
        (~branch_metadata_ex.branch_prediction_used) |
        (branch_metadata_ex.branch_predictor_metadata[1] ^ ex_entry.metadata[1]);

    assign observation_update_now = ({CONFIG.BP.WAYS{br_results.valid}} & (branch_metadata_ex.branch_predictor_update_way));
    assign tag_write_way = observation_update_now | inv_way_now; // write to all banks with pending updates or invalidation. Other logic will select addres for each case
    assign target_write_way = ({CONFIG.BP.WAYS{branch_predictor_direction_changed}} & tag_write_way) | inv_way_now;
    ////////////////////////////////////////////////////
    //Target PC if branch flush occured
    assign bp.branch_flush_pc = br_results.target_pc;

    ////////////////////////////////////////////////////
    //RAS support
    assign ras.branch_retired = br_results.valid & br_results.is_branch & branch_metadata_ex.branch_prediction_used;

endmodule
