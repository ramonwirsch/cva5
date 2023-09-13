
module fp_short_unit_sp
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    (
        input logic clk,
        input logic rst,

        input fp_short_inputs_t inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );

    logic valid;
    logic stage_advance;
    assign issue.ready = stage_advance;

    fp_short_op_t op_r; 
    id_t id_r;

    flopoco_t ieeeToFlopocoResult;
    flopoco_t ieeeToFlopocoResult_r;

    ieee_to_flopoco_sp ieeeToFlopoco ( // combinatorial
        .clk(clk),
        .X(inputs.rs1_gp),
        .R(ieeeToFlopocoResult)
    );

    logic XltY, XeqY, XleY;

    flopoco_t inputA_r, inputB_r;

    f_compare cmp ( // 1 cycle
        .clk(clk),
        .ce(stage_advance),
        .X(inputs.rs1),
        .Y(inputs.rs2),
        .unordered(),
        .XltY(XltY),
        .XeqY(XeqY),
        .XleY(XleY)
    );

    flopoco_t uintToFlopocoResult;
    flopoco_t intToFlopocoResult;

    logic [31:0] i2fInput;
    assign i2fInput = (inputs.op == FPCVT_FROM_I_OP && inputs.rs1_gp[31])? (~inputs.rs1_gp + 1) : inputs.rs1_gp;
    logic i2fInput_was_neg;

    fix_us_to_fp intToFlopoco ( // 1 cyc "flopoco4_fix2fp_2000MHz_us" file
        .clk(clk),
        .rst(rst),
        .ce(stage_advance),
        .I(i2fInput),
        .O(uintToFlopocoResult)
    );

    assign intToFlopocoResult = (i2fInput_was_neg)? {uintToFlopocoResult[33:32], 1'b1, uintToFlopocoResult[30:0]} : uintToFlopocoResult;


    always_ff @(posedge clk) begin
        if (rst)
            valid <= '0;
        else if (stage_advance) begin
            valid <= issue.new_request;
            id_r <= issue.id;
            op_r <= inputs.op;
            inputA_r <= inputs.rs1;
            inputB_r <= inputs.rs2;
            i2fInput_was_neg <= inputs.rs1_gp[31];
            ieeeToFlopocoResult_r <= ieeeToFlopocoResult;
        end
    end

    assign stage_advance = !valid || wb.ack;

    always_comb begin
        case (op_r)
        FPCVT_FROM_I_OP : begin
            wb.rd = intToFlopocoResult;
        end
        FPCVT_FROM_U_OP : begin
            wb.rd = uintToFlopocoResult;
        end
        FPMIN_OP : begin
            wb.rd = XltY? inputA_r : inputB_r;
        end
        FPMAX_OP : begin
            wb.rd = XltY? inputB_r : inputA_r;
        end
        /*FP_FROM_IEEE_OP*/ default : begin
            wb.rd = ieeeToFlopocoResult_r;
        end
        endcase
    end

    //WB interface
    ////////////////////////////////////////////////////
    assign wb.done = valid;
    assign wb.id = id_r;

endmodule : fp_short_unit_sp
