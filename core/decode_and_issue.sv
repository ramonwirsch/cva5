/*
 * Copyright © 2017-2019 Eric Matthews,  Lesley Shannon
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

module decode_and_issue

    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    import csr_types::*;

    # (
        parameter cpu_config_t CONFIG = EXAMPLE_CONFIG,
        parameter rf_params_t RF_CONFIG = get_derived_rf_params(CONFIG),
        parameter NUM_UNITS = 7,
        parameter unit_id_param_t UNIT_IDS = EXAMPLE_UNIT_IDS
    )

    (
        input logic clk,
        input logic rst,

        //ID Management
        input logic pc_id_available,
        input decode_packet_t decode,
        output logic decode_advance,
        output exception_sources_t decode_exception_unit,

        //Renamer
        renamer_interface.decode renamer,

        output logic decode_uses_rd_gp,
        output logic decode_uses_rd_fp,
        output rs_addr_t decode_rd_addr,
        output phys_addr_t decode_phys_rd_addr,
        output phys_addr_t decode_phys_rs_addr [MAX_RS_REG_COUNT_PER_INSN],
        output logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] decode_rs_wb_group [MAX_RS_REG_COUNT_PER_INSN],

        output logic instruction_issued,
        output logic instruction_issued_with_rd,
        output issue_packet_t issue,

        //Register File
        register_file_issue_interface.issue gp_rf,
        register_file_issue_interface.issue fp_rf,

        output alu_inputs_t alu_inputs,
        output load_store_inputs_t ls_inputs,
        output branch_inputs_t branch_inputs,
        output gc_inputs_t gc_inputs,
        output csr_inputs_t csr_inputs,
        output mul_inputs_t mul_inputs,
        output div_inputs_t div_inputs,
        output fp_mac_inputs_t fp_mac_inputs,
        output fp_div_sqrt_inputs_t fp_div_inputs,
        output fp_short_inputs_t fp_short_inputs,
        output fp_to_gp_inputs_t fp_to_gp_inputs,

        unit_issue_interface.decode unit_issue [NUM_UNITS-1:0],

        input gc_outputs_t gc,
        input logic [1:0] current_privilege,

        exception_interface.unit exception,

        //Trace signals
        output logic tr_operand_stall,
        output logic tr_unit_stall,
        output logic tr_no_id_stall,
        output logic tr_no_instruction_stall,
        output logic tr_other_stall,
        output logic tr_branch_operand_stall,
        output logic tr_alu_operand_stall,
        output logic tr_ls_operand_stall,
        output logic tr_div_operand_stall,

        output logic tr_alu_op,
        output logic tr_branch_or_jump_op,
        output logic tr_load_op,
        output logic tr_store_op,
        output logic tr_mul_op,
        output logic tr_div_op,
        output logic tr_misc_op,
        output logic tr_float_op,

        output logic tr_instruction_issued_dec,
        output logic [31:0] tr_instruction_pc_dec,
        output logic [31:0] tr_instruction_data_dec
        );

    logic [2:0] fn3;
    logic [6:0] opcode;
    logic [4:0] opcode_trim;
    logic [6:0] fn7;
    logic [4:0] fn7_trim;

    logic uses_rs [RF_CONFIG.TOTAL_READ_PORT_COUNT];
    logic uses_rd_for_gp;
    logic uses_rd_for_fp;

    rf_addr_t rs_addr [MAX_RS_REG_COUNT_PER_INSN];
    rs_addr_t rd_addr;

    logic is_csr;
    logic is_fence;
    logic is_ifence;
    logic csr_imm_op;
    logic environment_op;

    logic issue_valid;
    logic operands_ready;
    logic mult_div_op;

    logic [NUM_UNITS-1:0] unit_needed;
    logic [NUM_UNITS-1:0] unit_needed_issue_stage;
    logic [NUM_UNITS-1:0] unit_ready;
    logic [NUM_UNITS-1:0] issue_ready;
    logic [NUM_UNITS-1:0] issue_to;

    rf_addr_t issue_rs_addr [MAX_RS_REG_COUNT_PER_INSN];
    phys_addr_t issue_phys_rs_addr [MAX_RS_REG_COUNT_PER_INSN];
    logic [$clog2(RF_CONFIG.TOTAL_WB_GROUP_COUNT)-1:0] issue_rs_wb_group [MAX_RS_REG_COUNT_PER_INSN];
    logic issue_uses_rs [RF_CONFIG.TOTAL_READ_PORT_COUNT];

    logic pre_issue_exception_pending;
    logic illegal_instruction_pattern;

    logic issue_stage_ready;

    logic [RF_CONFIG.TOTAL_READ_PORT_COUNT-1:0] rs_conflict;

    genvar i;
    ////////////////////////////////////////////////////
    //Implementation
    
    //Can move data into issue stage if:
    // there is no instruction currently in the issue stage, or
    // an instruction could issue (issue_flush, issue_hold and whether the instruction is valid are not needed in this check)
    assign issue_stage_ready = ((~issue.stage_valid) | (issue_valid & |issue_ready)) & ~gc.issue_hold;
    assign decode_advance = decode.valid & issue_stage_ready;

    //Instruction aliases
    assign opcode = decode.instruction[6:0];
    assign opcode_trim = opcode[6:2];
    assign fn3 = decode.instruction[14:12];
    assign fn7 = decode.instruction[31:25];
    assign fn7_trim = fn7[6:2];
    assign rs_addr[RS1].rs = decode.instruction[19:15];
    assign rs_addr[RS2].rs = decode.instruction[24:20];
    assign rs_addr[RS3].rs = decode.instruction[31:27];
    assign rd_addr = decode.instruction[11:7];

    assign is_csr = CONFIG.INCLUDE_CSRS & (opcode_trim == SYSTEM_T) & (fn3 != 0);
    assign is_fence = (opcode_trim == FENCE_T) & ~fn3[0];
    assign is_ifence = CONFIG.INCLUDE_IFENCE & (opcode_trim == FENCE_T) & fn3[0];
    assign csr_imm_op = (opcode_trim == SYSTEM_T) & fn3[2];
    assign environment_op = (opcode_trim == SYSTEM_T) & (fn3 == 0);

    ////////////////////////////////////////////////////
    //Register File Support
    localparam RSG1 = 0;
    localparam RSG2 = 1;
    localparam RSF1 = 2;
    localparam RSF2 = 3;
    localparam RSF3 = 4;

    logic rsg1_by_float;
    logic rd_for_gp_float;

    assign rsg1_by_float = CONFIG.INCLUDE_FPU_SINGLE && (opcode_trim inside {FLW_T, FSW_T} || (opcode_trim == FP_T && fn7_trim inside {FCVT_TO_FP_fn7_T, FMV_TO_FP_fn7_T}));
    assign rd_for_gp_float = CONFIG.INCLUDE_FPU_SINGLE && (opcode_trim == FP_T && fn7_trim inside {FCVT_TO_GP_fn7_T, FCLASS_MV_TO_GP_fn7_T, FCMP_fn7_T});

    assign uses_rs[RSG1] = opcode_trim inside {JALR_T, BRANCH_T, LOAD_T, STORE_T, ARITH_IMM_T, ARITH_T, AMO_T} || is_csr || rsg1_by_float;
    assign uses_rs[RSG2] = opcode_trim inside {BRANCH_T, ARITH_T, AMO_T}; //Stores are exempted due to store forwarding
    assign uses_rd_for_gp = opcode_trim inside {LUI_T, AUIPC_T, JAL_T, JALR_T, LOAD_T, ARITH_IMM_T, ARITH_T} || is_csr || rd_for_gp_float;

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin: gen_fp_reg_decoding
        assign uses_rs[RSF1] = opcode_trim inside {FMADD_S_T, FMSUB_S_T, FNMADD_S_T, FNMSUB_S_T} || (opcode_trim == FP_T & !(fn7_trim inside {FMV_TO_FP_fn7_T, FCVT_TO_FP_fn7_T}));
        assign uses_rs[RSF2] = opcode_trim inside {FMADD_S_T, FMSUB_S_T, FNMADD_S_T, FNMSUB_S_T, FSW_T} || (opcode_trim == FP_T && !(fn7_trim inside {FCVT_TO_FP_fn7_T, FCVT_TO_GP_fn7_T, FMV_TO_FP_fn7_T, FSQRT_fn7_T, FCLASS_MV_TO_GP_fn7_T}));
        //TODO check if FSW also uses the forwarding that exempts rsg2 from use?
        assign uses_rs[RSF3] = opcode_trim inside {FMADD_S_T, FMSUB_S_T, FNMADD_S_T, FNMSUB_S_T};
        assign uses_rd_for_fp = opcode_trim inside {FLW_T, FMADD_S_T, FMSUB_S_T, FNMADD_S_T, FNMSUB_S_T, FP_T} && !(fn7_trim inside {FCVT_TO_GP_fn7_T, FCLASS_MV_TO_GP_fn7_T, FCMP_fn7_T});

        assign rs_addr[RS1].isFloat = uses_rs[RSF1];
        assign rs_addr[RS2].isFloat = uses_rs[RSF2];
        assign rs_addr[RS3].isFloat = 1;
    end else begin

        assign rs_addr[RS1].isFloat = 0;
        assign rs_addr[RS2].isFloat = 0;
        assign rs_addr[RS3].isFloat = 1;
        assign uses_rd_for_fp = 0;
    end endgenerate

    ////////////////////////////////////////////////////
    //Unit Determination
    assign unit_needed[UNIT_IDS.BR] = opcode_trim inside {BRANCH_T, JAL_T, JALR_T};
    assign unit_needed[UNIT_IDS.ALU] = (opcode_trim inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T, JAL_T, JALR_T}) && ~mult_div_op;
    assign unit_needed[UNIT_IDS.LS] = opcode_trim inside {LOAD_T, STORE_T, AMO_T} || is_fence || (CONFIG.INCLUDE_FPU_SINGLE && opcode_trim inside {FLW_T, FSW_T});
    generate if (CONFIG.INCLUDE_CSRS)
        assign unit_needed[UNIT_IDS.CSR] = is_csr;
    endgenerate
    assign unit_needed[UNIT_IDS.IEC] = (opcode_trim inside {SYSTEM_T} & ~is_csr & CONFIG.INCLUDE_M_MODE) | is_ifence;

    assign mult_div_op = (opcode_trim == ARITH_T) && decode.instruction[25];
    generate if (CONFIG.INCLUDE_MUL)
        assign unit_needed[UNIT_IDS.MUL] = mult_div_op && ~fn3[2];
    endgenerate

    generate if (CONFIG.INCLUDE_DIV)
        assign unit_needed[UNIT_IDS.DIV] = mult_div_op && fn3[2];
    endgenerate

    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin: gen_fpu_unit_sel
        assign unit_needed[UNIT_IDS.FP_MAC] = opcode_trim inside {FMADD_S_T, FMSUB_S_T, FNMADD_S_T, FNMSUB_S_T} || (opcode_trim == FP_T && (fn7_trim inside {FADD_fn7_T, FSUB_fn7_T, FMUL_fn7_T, FSGN_fn7_T}));
        assign unit_needed[UNIT_IDS.FP_DIV] = (opcode_trim == FP_T && (fn7_trim inside {FDIV_fn7_T, FSQRT_fn7_T}));
        assign unit_needed[UNIT_IDS.FP_SHORT] = (opcode_trim == FP_T && (fn7_trim inside {FMV_TO_FP_fn7_T, FCVT_TO_FP_fn7_T, FMUX_fn7_T}));
        assign unit_needed[UNIT_IDS.FP_TO_GP] = opcode_trim == FP_T && fn7_trim inside {FCVT_TO_GP_fn7_T, FCLASS_MV_TO_GP_fn7_T, FCMP_fn7_T};

        assign renamer.rd_wb_group = (unit_needed[UNIT_IDS.FP_MAC] || unit_needed[UNIT_IDS.FP_SHORT] || unit_needed[UNIT_IDS.FP_DIV] || opcode_trim == FLW_T)? 2 : (unit_needed[UNIT_IDS.ALU]? 0 : 1);
    end else begin
        assign renamer.rd_wb_group = ~unit_needed[UNIT_IDS.ALU];//TODO: automate generation of wb group logic
    end endgenerate

    ////////////////////////////////////////////////////
    //Renamer Support
    assign renamer.rd_addr = rd_addr;
    assign renamer.rs_addr = rs_addr;
    assign renamer.uses_rd_gp = uses_rd_for_gp;
    assign renamer.uses_rd_fp = uses_rd_for_fp;
    
    //TODO for now, only 1 FP write port, so rd_wb_group is D/C if uses_rd_fp is true
    assign renamer.id = decode.id;

    ////////////////////////////////////////////////////
    //Decode ID Support
    assign decode_uses_rd_gp = uses_rd_for_gp;
    assign decode_uses_rd_fp = uses_rd_for_fp;
    assign decode_rd_addr = rd_addr;
    assign decode_phys_rd_addr = renamer.phys_rd_addr;
    assign decode_phys_rs_addr = renamer.phys_rs_addr;
    assign decode_rs_wb_group = renamer.rs_wb_group;

    ////////////////////////////////////////////////////
    //Issue
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            issue.pc <= decode.pc;
            issue.instruction <= decode.instruction;
            issue.fetch_metadata <= decode.fetch_metadata;
            issue.fn3 <= fn3;
            issue.opcode <= opcode;
            issue_rs_addr <= rs_addr;
            issue_phys_rs_addr <= renamer.phys_rs_addr;
            issue_rs_wb_group <= renamer.rs_wb_group;
            issue.rd_addr <= {uses_rd_for_fp, rd_addr};
            issue.phys_rd_addr <= renamer.phys_rd_addr;
            issue.is_multicycle <= ~unit_needed[UNIT_IDS.ALU];
            issue.id <= decode.id;
            issue.exception_unit <= decode_exception_unit;
            issue_uses_rs <= uses_rs;
            issue.uses_rd <= uses_rd_for_gp || uses_rd_for_fp;
        end
    end

    always_ff @(posedge clk) begin
        if (issue_stage_ready)
            unit_needed_issue_stage <= unit_needed;
    end

    always_ff @(posedge clk) begin
        if (rst | gc.fetch_flush)
            issue.stage_valid <= 0;
        else if (issue_stage_ready)
            issue.stage_valid <= decode.valid;
    end

    ////////////////////////////////////////////////////
    //Unit ready
    generate for (i=0; i<NUM_UNITS; i++)
        assign unit_ready[i] = unit_issue[i].ready;
    endgenerate

    ////////////////////////////////////////////////////
    //Issue Determination
    generate
        for (i=0; i< RF_CONFIG.GP_READ_PORT_COUNT; i++)
            assign rs_conflict[i] = gp_rf.inuse[1'(i)] && issue_uses_rs[i];
        for (i=RF_CONFIG.GP_READ_PORT_COUNT; i < RF_CONFIG.TOTAL_READ_PORT_COUNT; i++)
            assign rs_conflict[i] = fp_rf.inuse[i-RF_CONFIG.GP_READ_PORT_COUNT] && issue_uses_rs[i];
    endgenerate
    assign operands_ready = ~|rs_conflict;

    assign issue_ready = unit_needed_issue_stage & unit_ready;
    assign issue_valid = issue.stage_valid & operands_ready & ~gc.issue_hold & ~pre_issue_exception_pending;

    assign issue_to = {NUM_UNITS{issue_valid & ~gc.fetch_flush}} & issue_ready;

    assign instruction_issued = issue_valid & ~gc.fetch_flush & |issue_ready;
    assign instruction_issued_with_rd = instruction_issued & issue.uses_rd;

    ////////////////////////////////////////////////////
    //Register File Issue Interface
    assign gp_rf.phys_rs_addr = issue_phys_rs_addr[RS1:RS2];
    assign gp_rf.phys_rd_addr = issue.phys_rd_addr;
    assign gp_rf.rs_wb_group = '{ issue_rs_wb_group[RS1][0], issue_rs_wb_group[RS2][0]};
    
    assign gp_rf.single_cycle_or_flush = (instruction_issued_with_rd & |issue.rd_addr & ~issue.is_multicycle) | (issue.stage_valid & issue.uses_rd & !issue.rd_addr.isFloat & |issue.rd_addr & gc.fetch_flush);

    assign fp_rf.phys_rs_addr = issue_phys_rs_addr[RS1:RS3];
    assign fp_rf.phys_rd_addr = issue.phys_rd_addr;
    assign fp_rf.rs_wb_group = '{0, 0, 0};
    assign fp_rf.single_cycle_or_flush = issue.stage_valid && issue.uses_rd && issue.rd_addr.isFloat && gc.fetch_flush;
    
    ////////////////////////////////////////////////////
    //ALU unit inputs
    logic [XLEN-1:0] alu_rs2_data;
    logic alu_imm_type;
    logic [31:0] constant_alu;
    alu_op_t alu_op;
    alu_op_t alu_op_r;
    alu_logic_op_t alu_logic_op;
    alu_logic_op_t alu_logic_op_r;
    logic alu_subtract;
    logic sub_instruction;

    always_comb begin
        case (opcode_trim) inside
            LUI_T, AUIPC_T, JAL_T, JALR_T : alu_op = ALU_CONSTANT;
            default : 
            case (fn3) inside
                SLTU_fn3, SLT_fn3 : alu_op = ALU_SLT;
                SLL_fn3, SRA_fn3 : alu_op = ALU_SHIFT;
                default : alu_op = ALU_ADD_SUB;
            endcase
        endcase
    end

    always_comb begin
        case (fn3)
            XOR_fn3 : alu_logic_op = ALU_LOGIC_XOR;
            OR_fn3 : alu_logic_op = ALU_LOGIC_OR;
            AND_fn3 : alu_logic_op = ALU_LOGIC_AND;
            default : alu_logic_op = ALU_LOGIC_ADD;//ADD/SUB/SLT/SLTU
        endcase
    end

    assign sub_instruction = (fn3 == ADD_SUB_fn3) && decode.instruction[30] && opcode[5];//If ARITH instruction

    //Constant ALU:
    //  provides LUI, AUIPC, JAL, JALR results for ALU
    //  provides PC+4 for BRANCH unit and ifence in GC unit
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            constant_alu <= ((opcode_trim inside {LUI_T}) ? '0 : decode.pc) + ((opcode_trim inside {LUI_T, AUIPC_T}) ? {decode.instruction[31:12], 12'b0} : 4); 
            alu_imm_type <= opcode_trim inside {ARITH_IMM_T};
            alu_op_r <= alu_op;
            alu_subtract <= (fn3 inside {SLTU_fn3, SLT_fn3}) || sub_instruction;
            alu_logic_op_r <= alu_logic_op;
        end
    end

    //Shifter related
    assign alu_inputs.lshift = ~issue.fn3[2];
    assign alu_inputs.shift_amount = alu_imm_type ? issue_rs_addr[RS2].rs : gp_rf.data[RSG2][4:0];
    assign alu_inputs.arith = gp_rf.data[RSG1][XLEN-1] & issue.instruction[30];//shift in bit
    assign alu_inputs.shifter_in = gp_rf.data[RSG1];

    //LUI, AUIPC, JAL, JALR
    assign alu_inputs.constant_adder = constant_alu;

    //logic and adder
    assign alu_inputs.subtract = alu_subtract;
    assign alu_inputs.logic_op = alu_logic_op_r;
    assign alu_inputs.in1 = {(gp_rf.data[RSG1][XLEN-1] & ~issue.fn3[0]), gp_rf.data[RSG1]};//(fn3[0]  is SLTU_fn3);
    assign alu_rs2_data = alu_imm_type ? 32'(signed'(issue.instruction[31:20])) : gp_rf.data[RSG2];
    assign alu_inputs.in2 = {(alu_rs2_data[XLEN-1] & ~issue.fn3[0]), alu_rs2_data};

    assign alu_inputs.alu_op = alu_op_r;
    ////////////////////////////////////////////////////
    //Load Store unit inputs
    logic is_load;
    logic is_store;
    logic is_float_load;
    logic is_float_store;
    logic amo_op;
    logic store_conditional;
    logic load_reserve;
    logic [4:0] amo_type;

    assign amo_op =  CONFIG.INCLUDE_AMO ? (opcode_trim == AMO_T) : 1'b0;
    assign amo_type = decode.instruction[31:27];
    assign store_conditional = (amo_type == AMO_SC_FN5);
    assign load_reserve = (amo_type == AMO_LR_FN5);
    assign is_float_load = CONFIG.INCLUDE_FPU_SINGLE && opcode_trim inside {FLW_T};
    assign is_float_store = CONFIG.INCLUDE_FPU_SINGLE && opcode_trim inside {FSW_T};


    generate if (CONFIG.INCLUDE_AMO) begin : gen_decode_ls_amo
            assign ls_inputs.amo.is_lr = load_reserve;
            assign ls_inputs.amo.is_sc = store_conditional;
            assign ls_inputs.amo.is_amo = amo_op & ~(load_reserve | store_conditional);
            assign ls_inputs.amo.op = amo_type;
        end
        else begin
            assign ls_inputs.amo = '0;
        end
    endgenerate

    assign is_load = ((opcode_trim inside {LOAD_T, AMO_T}) && !(amo_op & store_conditional)) || is_float_load; //LR and AMO_ops perform a read operation as well
    assign is_store = (opcode_trim inside {STORE_T}) || (amo_op && store_conditional) || is_float_store;//Used for LS unit and for ID tracking

    logic [11:0] ls_offset;
    logic is_load_r;
    logic is_store_r;
    logic is_fence_r;
    logic is_float_r;
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            ls_offset <= opcode[5] ? {decode.instruction[31:25], decode.instruction[11:7]} : decode.instruction[31:20];
            is_load_r <= is_load;
            is_store_r <= is_store;
            is_fence_r <= is_fence;
            is_float_r <= is_float_load || is_float_store;
        end
    end

    localparam RELEVANT_RD_BITS = $clog2(RF_CONFIG.TOTAL_ISA_REGS);

    (* ramstyle = "MLAB, no_rw_check" *) id_t rd_to_id_table [RF_CONFIG.TOTAL_ISA_REGS];
    always_ff @ (posedge clk) begin
        if (instruction_issued_with_rd)
            rd_to_id_table[issue.rd_addr[RELEVANT_RD_BITS-1:0]] <= issue.id;
    end

    assign ls_inputs.offset = ls_offset;
    assign ls_inputs.load = is_load_r;
    assign ls_inputs.store = is_store_r;
    assign ls_inputs.fence = is_fence_r;
    assign ls_inputs.fn3 = amo_op ? LS_W_fn3 : issue.fn3;
    assign ls_inputs.rs1 = gp_rf.data[RSG1]; // addr
    assign ls_inputs.rs2 = is_float_r? fp_rf.data[RS2] : {2'b00, gp_rf.data[RSG2]}; // data if store
    assign ls_inputs.is_float = is_float_r;
    assign ls_inputs.forwarded_store = (is_float_r && is_store_r)? fp_rf.inuse[RS2] : gp_rf.inuse[RSG2];
    assign ls_inputs.store_forward_id = rd_to_id_table[issue_rs_addr[RS2][RELEVANT_RD_BITS-1:0]]; // RS-bits in insn are identical for GP & FP

    ////////////////////////////////////////////////////
    //Branch unit inputs

    ////////////////////////////////////////////////////
    //RAS Support
    logic rs1_link;
    logic rd_link;
    logic rs1_eq_rd;
    logic is_return;
    logic is_call;
    assign rs1_link = (rs_addr[RS1].rs inside {1,5});
    assign rd_link = (rd_addr inside {1,5});
    assign rs1_eq_rd = (rs_addr[RS1].rs == rd_addr);

    logic br_use_signed;

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_return <= (opcode_trim == JALR_T) && ((rs1_link & ~rd_link) | (rs1_link & rd_link & ~rs1_eq_rd));
            is_call <= (opcode_trim inside {JAL_T, JALR_T}) && rd_link;
            br_use_signed <= !(fn3 inside {BLTU_fn3, BGEU_fn3});
        end
    end

    logic[19:0] jal_imm;
    logic[11:0] jalr_imm;
    logic[11:0] br_imm;

    logic [20:0] pc_offset;
    logic [20:0] pc_offset_r;
    assign jal_imm = {decode.instruction[31], decode.instruction[19:12], decode.instruction[20], decode.instruction[30:21]};
    assign jalr_imm = decode.instruction[31:20];
    assign br_imm = {decode.instruction[31], decode.instruction[7], decode.instruction[30:25], decode.instruction[11:8]};


    always_comb begin
        case (opcode[3:2])
            2'b11 : pc_offset = 21'(signed'({jal_imm, 1'b0}));
            2'b01 : pc_offset = 21'(signed'(jalr_imm));
            default : pc_offset = 21'(signed'({br_imm, 1'b0}));
        endcase
    end

    logic jalr;
    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            pc_offset_r <= pc_offset;
            jalr <= (~opcode[3] & opcode[2]);
        end
    end

    assign branch_inputs.is_return = is_return;
    assign branch_inputs.is_call = is_call;
    assign branch_inputs.fn3 = issue.fn3;
    assign branch_inputs.pc_offset = pc_offset_r;
    assign branch_inputs.jal = issue.opcode[3];//(opcode == JAL);
    assign branch_inputs.jalr = jalr;
    assign branch_inputs.jal_jalr = issue.opcode[2];

    assign branch_inputs.issue_pc = issue.pc;
    assign branch_inputs.issue_pc_valid = issue.stage_valid;
    assign branch_inputs.rs1 = {(gp_rf.data[RSG1][31] & br_use_signed), gp_rf.data[RSG1]};
    assign branch_inputs.rs2 = {(gp_rf.data[RSG2][31] & br_use_signed), gp_rf.data[RSG2]};
    assign branch_inputs.pc_p4 = constant_alu;

    ////////////////////////////////////////////////////
    //Global Control unit inputs
    logic is_ecall_r;
    logic is_ebreak_r;
    logic is_mret_r;
    logic is_sret_r;
    logic is_ifence_r;

    logic [7:0] sys_op_match;
    typedef enum logic [2:0] {
        ECALL_i = 0,
        EBREAK_i = 1,
        URET_i = 2,
        SRET_i = 3,
        MRET_i = 4,
        SFENCE_i = 5
    } sys_op_index_t;

    always_comb begin
        sys_op_match = '0;
        case (decode.instruction[31:20]) inside
            ECALL_imm : sys_op_match[ECALL_i] = CONFIG.INCLUDE_M_MODE;
            EBREAK_imm : sys_op_match[EBREAK_i] = CONFIG.INCLUDE_M_MODE;
            SRET_imm : sys_op_match[SRET_i] = CONFIG.INCLUDE_S_MODE;
            MRET_imm : sys_op_match[MRET_i] = CONFIG.INCLUDE_M_MODE;
            SFENCE_imm : sys_op_match[SFENCE_i] = CONFIG.INCLUDE_S_MODE;
            default : sys_op_match = '0;
        endcase
    end

    always_ff @(posedge clk) begin
        if (issue_stage_ready) begin
            is_ecall_r <= sys_op_match[ECALL_i];
            is_ebreak_r <= sys_op_match[EBREAK_i];
            is_mret_r <= sys_op_match[MRET_i];
            is_sret_r <= sys_op_match[SRET_i];
            is_ifence_r <= is_ifence;
        end
    end

    assign gc_inputs.pc_p4 = constant_alu;
    assign gc_inputs.is_ifence = is_ifence_r;
    assign gc_inputs.is_mret = is_mret_r;
    assign gc_inputs.is_sret = is_sret_r;

    ////////////////////////////////////////////////////
    //CSR unit inputs
    generate if (CONFIG.INCLUDE_CSRS) begin : gen_decode_csr_inputs
        assign csr_inputs.addr = issue.instruction[31:20];
        assign csr_inputs.op = issue.fn3[1:0];
        assign csr_inputs.data = issue.fn3[2] ? {27'b0, issue_rs_addr[RS1].rs} : gp_rf.data[RSG1];
        assign csr_inputs.reads = ~((issue.fn3[1:0] == CSR_RW) && (issue.rd_addr == 0));
        assign csr_inputs.writes = ~((issue.fn3[1:0] == CSR_RC) && (issue_rs_addr[RS1].rs == 0));
    end endgenerate

    ////////////////////////////////////////////////////
    //Mul unit inputs
    generate if (CONFIG.INCLUDE_MUL) begin : gen_decode_mul_inputs
        assign mul_inputs.rs1 = gp_rf.data[RSG1];
        assign mul_inputs.rs2 = gp_rf.data[RSG2];
        assign mul_inputs.op = issue.fn3[1:0];
    end endgenerate

    ////////////////////////////////////////////////////
    //Div unit inputs
    generate if (CONFIG.INCLUDE_DIV) begin : gen_decode_div_inputs
        phys_addr_t prev_div_rs_addr [2];
        logic [1:0] div_rd_match;
        logic prev_div_result_valid;
        logic div_rs_overwrite;
        logic div_op_reuse;

        always_ff @(posedge clk) begin
            if (issue_to[UNIT_IDS.DIV])
                prev_div_rs_addr <= issue_phys_rs_addr[RS1:RS2];
        end

        assign div_op_reuse = {prev_div_result_valid, prev_div_rs_addr[RSG1], prev_div_rs_addr[RSG2]} == {1'b1, issue_phys_rs_addr[RSG1],issue_phys_rs_addr[RSG2]};

        //Clear if prev div inputs are overwritten by another instruction
        assign div_rd_match[RSG1] = (issue.phys_rd_addr == prev_div_rs_addr[RSG1]);
        assign div_rd_match[RSG2] = (issue.phys_rd_addr == prev_div_rs_addr[RSG2]);
        assign div_rs_overwrite = |div_rd_match;

        set_clr_reg_with_rst #(.SET_OVER_CLR(1), .WIDTH(1), .RST_VALUE(0)) prev_div_result_valid_m (
            .clk, .rst,
            .set(instruction_issued & unit_needed_issue_stage[UNIT_IDS.DIV]),
            .clr((instruction_issued & issue.uses_rd & !issue.rd_addr.isFloat & div_rs_overwrite) | gc.writeback_supress), //No instructions will be issued while gc.writeback_supress is asserted
            .result(prev_div_result_valid)
        );

        assign div_inputs.rs1 = gp_rf.data[RSG1];
        assign div_inputs.rs2 = gp_rf.data[RSG2];
        assign div_inputs.op = issue.fn3[1:0];
        assign div_inputs.reuse_result = div_op_reuse;
    end endgenerate

    ////////////////////////////////////////////////////
    //FPU unit inputs
    generate if (CONFIG.INCLUDE_FPU_SINGLE) begin : gen_decode_fpu_inputs
        fp_mac_op_t fp_mac_op;
        fp_mac_op_t fp_mac_op_r;
        logic fp_div_sqrt;
        logic fp_div_sqrt_r;
        fp_short_op_t fp_short_op;
        fp_short_op_t fp_short_op_r;
        fp_to_gp_op_t fp_to_gp_op;
        fp_to_gp_op_t fp_to_gp_op_r;


        always_comb begin
            
            fp_mac_op.mul = 0;
            fp_mac_op.add_mul_rs3 = 0;
            fp_mac_op.add_rs1_rs2 = 0;
            fp_mac_op.ovr_1st_add_in_sign = ORG_A_SIGN;
            fp_mac_op.negate_2nd_add_in = 0;

            if (opcode_trim inside {FMADD_S_T, FMSUB_S_T, FNMADD_S_T, FNMSUB_S_T}) begin
                fp_mac_op.mul = 1;
                fp_mac_op.add_mul_rs3 = 1;
                if (opcode_trim inside {FNMADD_S_T, FNMSUB_S_T})
                    fp_mac_op.ovr_1st_add_in_sign = INV_A_SIGN;
                fp_mac_op.negate_2nd_add_in = opcode_trim inside {FMSUB_S_T, FNMSUB_S_T};
            end else begin
                case (fn7_trim)
                    FADD_fn7_T : begin
                        fp_mac_op.add_rs1_rs2 = 1;
                    end
                    FSUB_fn7_T : begin
                        fp_mac_op.add_rs1_rs2 = 1;
                        fp_mac_op.negate_2nd_add_in = 1;
                    end
                    FMUL_fn7_T : begin
                        fp_mac_op.mul = 1;
                    end
                    /*FSGN_fn7_T*/ default: begin
                        case (fn3)
                            FMAX_FLT_FCLASS_FSGNJN_fn3 : fp_mac_op.ovr_1st_add_in_sign = INV_B_SIGN;
                            FEQ_FSGNJX_fn3 : fp_mac_op.ovr_1st_add_in_sign = XOR_SIGNS;
                            default : fp_mac_op.ovr_1st_add_in_sign = ORG_B_SIGN;
                        endcase
                    end
                    // default handled by initializing all op-bits to zero
                endcase
            end

            case (fn7_trim)
                FSQRT_fn7_T : fp_div_sqrt = 1;
                default: fp_div_sqrt = 0;
            endcase

            case (fn7_trim)
                FMUX_fn7_T : begin
                    case(fn3[0])
                        0 : fp_short_op = FPMIN_OP;
                        default : fp_short_op = FPMAX_OP;
                    endcase
                end
                FCVT_TO_FP_fn7_T : begin
                    case(rs_addr[RS2].rs[0])
                        0 : fp_short_op = FPCVT_FROM_I_OP;
                        default : fp_short_op = FPCVT_FROM_U_OP;
                    endcase
                end
                /*FMV_TO_FP_fn7_T*/ default : fp_short_op = FP_FROM_IEEE_OP;
            endcase

            case (fn7_trim)
                FCLASS_MV_TO_GP_fn7_T : begin
                    case(fn3[0])
                        0 : fp_to_gp_op = FP_TO_IEEE_OP;
                        default : fp_to_gp_op = FPCLASS_OP;
                    endcase
                end
                FCVT_TO_GP_fn7_T : begin
                    case(fn3[0])
                        0 : fp_to_gp_op = FPCVT_TO_I_OP;
                        default : fp_to_gp_op = FPCVT_TO_U_OP;
                    endcase
                end
                FCMP_fn7_T : begin
                    case (fn3)
                        FMIN_FMV_FLE_FSGNJ_fn3 : fp_to_gp_op = FPLE_OP;
                        FMAX_FLT_FCLASS_FSGNJN_fn3 : fp_to_gp_op = FPLT_OP;
                        default : fp_to_gp_op = FPEQ_OP;
                    endcase
                end
                default : fp_to_gp_op = FP_TO_IEEE_OP;
            endcase
        end

        always_ff @(posedge clk) begin
            if (issue_stage_ready) begin
                fp_mac_op_r <= fp_mac_op;
                fp_div_sqrt_r <= fp_div_sqrt;
                fp_short_op_r <= fp_short_op;
                fp_to_gp_op_r <= fp_to_gp_op;
            end
        end

        assign fp_mac_inputs.rs1 = fp_rf.data[RS1];
        assign fp_mac_inputs.rs2 = fp_rf.data[RS2];
        assign fp_mac_inputs.rs3 = fp_rf.data[RS3];
        assign fp_mac_inputs.op = fp_mac_op_r;

        assign fp_to_gp_inputs.rs1 = fp_rf.data[RS1];
        assign fp_to_gp_inputs.rs2 = fp_rf.data[RS2];
        assign fp_to_gp_inputs.op = fp_to_gp_op_r;

        assign fp_div_inputs.rs1 = fp_rf.data[RS1];
        assign fp_div_inputs.rs2 = fp_rf.data[RS2];
        assign fp_div_inputs.sqrt = fp_div_sqrt_r;

        assign fp_short_inputs.rs1 = fp_rf.data[RS1];
        assign fp_short_inputs.rs1_gp = gp_rf.data[RSG1];
        assign fp_short_inputs.rs2 = fp_rf.data[RS2];
        assign fp_short_inputs.op = fp_short_op_r;
    end endgenerate

    ////////////////////////////////////////////////////
    //Unit EX signals
    generate for (i = 0; i < NUM_UNITS; i++) begin : gen_unit_issue_signals
        assign unit_issue[i].possible_issue = issue.stage_valid & unit_needed_issue_stage[i] & unit_issue[i].ready;
        assign unit_issue[i].new_request = issue_to[i];
        assign unit_issue[i].id = issue.id;
    end endgenerate

    ////////////////////////////////////////////////////
    //Illegal Instruction check
    logic illegal_instruction_pattern_r;
    generate if (CONFIG.INCLUDE_M_MODE) begin : gen_decode_exceptions
    illegal_instruction_checker # (.CONFIG(CONFIG))
    illegal_op_check (
        .instruction(decode.instruction), .illegal_instruction(illegal_instruction_pattern)
    );
    always_ff @(posedge clk) begin
        if (rst)
            illegal_instruction_pattern_r <= 0;
        else if (issue_stage_ready)
            illegal_instruction_pattern_r <= illegal_instruction_pattern;
    end

    //TODO: Consider ways of parameterizing so that any exception generating unit
    //can be automatically added to this expression
    always_comb begin
        unique case (1'b1)
            unit_needed[UNIT_IDS.LS] : decode_exception_unit = LS_EXCEPTION;
            unit_needed[UNIT_IDS.BR] : decode_exception_unit = BR_EXCEPTION;
            default : decode_exception_unit = PRE_ISSUE_EXCEPTION;
        endcase
        if (illegal_instruction_pattern)
            decode_exception_unit = PRE_ISSUE_EXCEPTION;
    end

    ////////////////////////////////////////////////////
    //ECALL/EBREAK
    //The type of call instruction is depedent on the current privilege level
    exception_code_t ecall_code;
    always_comb begin
        case (current_privilege)
            USER_PRIVILEGE : ecall_code = ECALL_U;
             SUPERVISOR_PRIVILEGE : ecall_code = ECALL_S;
            MACHINE_PRIVILEGE : ecall_code = ECALL_M;
            default : ecall_code = ECALL_U;
        endcase
    end

    ////////////////////////////////////////////////////
    //Exception generation (ecall/ebreak/illegal instruction/propagated fetch error)
    logic new_exception;
    exception_code_t ecode;

    always_ff @(posedge clk) begin
        if (rst)
            pre_issue_exception_pending <= 0;
        else if (issue_stage_ready)
            pre_issue_exception_pending <= illegal_instruction_pattern | (opcode_trim inside {SYSTEM_T} & ~is_csr & (sys_op_match[ECALL_i] | sys_op_match[EBREAK_i])) | ~decode.fetch_metadata.ok;
    end

    assign new_exception = issue.stage_valid & pre_issue_exception_pending & ~(gc.issue_hold | gc.fetch_flush);

    always_ff @(posedge clk) begin
        if (rst)
            exception.valid <= 0;
        else
            exception.valid <= (exception.valid | new_exception) & ~exception.ack;
    end

    assign ecode =
        illegal_instruction_pattern_r ? ILLEGAL_INST :
        is_ecall_r ? ecall_code :
        ~issue.fetch_metadata.ok ? issue.fetch_metadata.error_code :
        BREAK;

    always_ff @(posedge clk) begin
        if (new_exception) begin
            exception.code <= ecode;
            exception.tval <= issue.instruction;
            exception.id <= issue.id;
        end
    end

    end endgenerate
    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface
    generate if (ENABLE_TRACE_INTERFACE) begin : gen_decode_trace
        assign tr_operand_stall = issue.stage_valid & ~gc.fetch_flush & ~gc.issue_hold & ~pre_issue_exception_pending & ~operands_ready & |issue_ready;
        assign tr_unit_stall = issue_valid & ~gc.fetch_flush & ~|issue_ready;
        assign tr_no_id_stall = (~issue.stage_valid & ~pc_id_available & ~gc.fetch_flush); //All instructions in execution pipeline
        assign tr_no_instruction_stall = (pc_id_available & ~issue.stage_valid) | gc.fetch_flush;
        assign tr_other_stall = issue.stage_valid & ~instruction_issued & ~(tr_operand_stall | tr_unit_stall | tr_no_id_stall | tr_no_instruction_stall);
        assign tr_branch_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.BR];
        assign tr_alu_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.ALU] & ~unit_needed_issue_stage[UNIT_IDS.BR];
        assign tr_ls_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.LS];
        assign tr_div_operand_stall = tr_operand_stall & unit_needed_issue_stage[UNIT_IDS.DIV];

        //Instruction Mix
        assign tr_alu_op = issue_stage_ready && instruction_issued && (issue.instruction[6:2] inside {ARITH_T, ARITH_IMM_T, AUIPC_T, LUI_T} && ~tr_mul_op && ~tr_div_op);
		assign tr_branch_or_jump_op = issue_stage_ready && instruction_issued && (issue.instruction[6:2] inside {JAL_T, JALR_T, BRANCH_T});
		assign tr_load_op = issue_stage_ready && instruction_issued && (issue.instruction[6:2] inside {LOAD_T, AMO_T});
		assign tr_store_op = issue_stage_ready && instruction_issued && (issue.instruction[6:2] inside {STORE_T});
		assign tr_mul_op = issue_stage_ready && instruction_issued && unit_needed_issue_stage[UNIT_IDS.MUL];
		assign tr_div_op = issue_stage_ready && instruction_issued && unit_needed_issue_stage[UNIT_IDS.DIV];
        assign tr_float_op = issue_stage_ready && instruction_issued && (unit_needed_issue_stage[UNIT_IDS.FP_MAC] || unit_needed_issue_stage[UNIT_IDS.FP_DIV] || unit_needed_issue_stage[UNIT_IDS.FP_SHORT] || unit_needed_issue_stage[UNIT_IDS.FP_TO_GP]);
		assign tr_misc_op = issue_stage_ready && instruction_issued && ~(tr_alu_op | tr_branch_or_jump_op | tr_load_op | tr_store_op | tr_mul_op | tr_div_op | tr_float_op);

        assign tr_instruction_issued_dec = instruction_issued;
        assign tr_instruction_pc_dec = issue.pc;
        assign tr_instruction_data_dec = issue.instruction;
    end endgenerate

endmodule
