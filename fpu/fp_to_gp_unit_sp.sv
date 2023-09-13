module fp_to_gp_unit_sp
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    (
        input logic clk,
        input logic rst,

        input fp_to_gp_inputs_t inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );

    logic valid;
    logic stage_advance;


    logic [31:0] toIeeeResult;
    logic [31:0] toIeeeResult_r;

    flopoco_to_ieee_sp toIeee ( // combinatorial
        .clk(clk),
        .X(inputs.rs1),
        .R(toIeeeResult)
    );

    logic [31:0] toUnsignedIntResult;

    fp_to_fix_us to32b( // 1 cycle
        .clk(clk),
        .ce(stage_advance),
        .I(inputs.rs1),
        .O(toUnsignedIntResult)
    );

    logic [31:0] toSignedIntResult;
    logic invalidToIntResult;

    assign invalidToIntResult = ((inputs.op == FPCVT_TO_I_OP) && toUnsignedIntResult[31]) || (inputs.op == FPCVT_TO_U_OP && inputs.rs1[31]); // input is larger than 2^31-1 and supposed to be signed or input is negative when unsigned
    assign toSignedIntResult = (toUnsignedIntResult[31])? {1'b0,  {31{1'b1}}} : -{1'b0, toUnsignedIntResult[30:0]};

    logic XltY, XeqY, XleY;

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

    logic [31:0] cmpEqResult;
    assign cmpEqResult = {31'b0, XeqY};
    logic [31:0] cmpLeResult;
    assign cmpLeResult = {31'b0, XleY};
    logic [31:0] cmpLtResult;
    assign cmpLtResult = {31'b0, XltY};


    logic [31:0] classifyResult;
    assign classifyResult[31:10] = '0;
    assign classifyResult[2] = 0;
    assign classifyResult[5] = 0;
    assign classifyResult[8] = 0;
    logic [31:0] classifyResult_r;

    fp_rv_classify_sp classify ( // combinatorial
        .fpInput(inputs.rs1),
        .isInfNeg(classifyResult[0]),
        .isNegNormNum(classifyResult[1]),
        .isNegNull(classifyResult[3]),
        .isPosNull(classifyResult[4]),
        .isPosNormNum(classifyResult[6]),
        .isInfPos(classifyResult[7]),
        .isQuietNAN(classifyResult[9])
    );

    fp_to_gp_op_t op_r; 
    id_t id_r;

    always_ff @(posedge clk) begin
        if (rst)
            valid <= '0;
        else if (stage_advance) begin
            valid <= issue.new_request;
            id_r <= issue.id;
            op_r <= inputs.op;
            classifyResult_r <= classifyResult;
            toIeeeResult_r <= toIeeeResult;
        end
    end

    assign stage_advance = !valid || wb.ack;
    assign issue.ready = stage_advance;


    //WB interface
    ////////////////////////////////////////////////////
    always_comb begin
        case (op_r)
        FPCVT_TO_I_OP : begin
            wb.rd[31:0] = toSignedIntResult;
        end
        FPCVT_TO_U_OP : begin
            wb.rd[31:0] = toUnsignedIntResult;
        end
        FPEQ_OP : begin
            wb.rd[31:0] = cmpEqResult;
        end
        FPLT_OP : begin
            wb.rd[31:0] = cmpLtResult;
        end
        FPLE_OP : begin
            wb.rd[31:0] = cmpLeResult;
        end
        FPCLASS_OP : begin
            wb.rd[31:0] = classifyResult_r;
        end
        /*FP_TO_IEEE_OP*/ default : begin
            wb.rd[31:0] = toIeeeResult_r;
        end
        endcase
    end
    assign wb.done = valid;
    assign wb.id = id_r;

endmodule : fp_to_gp_unit_sp
