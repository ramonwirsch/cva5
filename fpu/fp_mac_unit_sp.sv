

module fp_mac_unit_sp
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    (
        input logic clk,
        input logic rst,

        input fp_mac_inputs_t inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );

    logic input_advance;
    logic mul_advance;
    logic addIn_advance; // stage0 of add
    logic add_advance; // stage1-2 of add

    typedef struct packed {
        fp_mac_op_t op;
        id_t id;
    } stage_state_t;

    logic valid_input;
    fp_mac_inputs_t input_buf;
    id_t input_id_buf;

    localparam MUL_STAGES = 3; // including in & out buffers // code below relies on min 2 stages

    logic valid_mul [MUL_STAGES];
    stage_state_t state_mul [MUL_STAGES];

    localparam ADD_STAGES = 4; // including in & out buffers // code below relies on min 2 stages

    logic valid_add [ADD_STAGES];
    stage_state_t state_add [ADD_STAGES];


    assign issue.ready = input_advance;
    assign input_advance = !valid_input || (input_buf.op.mul && mul_advance) || (!input_buf.op.mul && add_advance);

    always_ff @(posedge clk) begin
        if (rst) begin
            valid_input <= 0;
        end else if (input_advance) begin
            valid_input <= issue.new_request;
        end
        if (input_advance) begin
            input_buf <= inputs;
            input_id_buf <= issue.id;
        end
    end

    flopoco_t mulInputA_r, mulInputB_r;

    flopoco_t mulResult;
    flopoco_t mulResult_r;

    flopoco_t mul_rs3_buf [MUL_STAGES];

    logic start_mul;
    assign start_mul = valid_input && input_buf.op.mul;
    logic mul_out_taken;
    assign mul_advance = !valid_mul[MUL_STAGES-1] || mul_out_taken;

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=0; i < MUL_STAGES; i++)
                valid_mul[i] <= 0;
        end else if (mul_advance) begin
            valid_mul[0] <= start_mul;
            for (int i=1; i < MUL_STAGES; i++)
                valid_mul[i] <= valid_mul[i-1];
        end
        if (mul_advance) begin
            mulInputA_r <= input_buf.rs1;
            mulInputB_r <= input_buf.rs2;
            mul_rs3_buf[0] <= input_buf.rs3;
            state_mul[0] <= '{ op: input_buf.op, id: input_id_buf};
            for (int i=1; i < MUL_STAGES; i++) begin
                mul_rs3_buf[i] <= mul_rs3_buf[i-1];
                state_mul[i] <= state_mul[i-1];
            end
            mulResult_r <= mulResult;
        end
    end

    f_mul mul( // 1cyc, (needs input + output buffers)
        .clk(clk),
        .ce(mul_advance),
        .X(mulInputA_r),
        .Y(mulInputB_r),
        .R(mulResult)
    );

    logic addMode_mulResult;
    logic start_add_in;
    logic start_add;
    logic add_takes_mul;

    flopoco_t adderInputA_org, adderInputA, adderInputB_org, adderInputB;
    flopoco_t adderInputA_r, adderInputB_r;
    flopoco_t adderResult;
    flopoco_t adderResult_r;

    assign adderInputA_org = addMode_mulResult? mulResult_r : input_buf.rs1;
    logic newSignA;
    assign adderInputA = {adderInputA_org[33:32], newSignA, adderInputA_org[30:0]};
    assign adderInputB_org = addMode_mulResult? mul_rs3_buf[MUL_STAGES-1] : input_buf.rs2;
    logic invert_adderInputB;
    assign invert_adderInputB = addMode_mulResult? state_mul[MUL_STAGES-1].op.negate_2nd_add_in : input_buf.op.negate_2nd_add_in;
    assign adderInputB = {adderInputB_org[33:32], invert_adderInputB ^ adderInputB_org[31], adderInputB_org[30:0]};
    sign_mod_t ovr_sign_mode;
    assign ovr_sign_mode = addMode_mulResult? state_mul[MUL_STAGES-1].op.ovr_1st_add_in_sign : input_buf.op.ovr_1st_add_in_sign;
    logic will_need_adder;

    always_comb begin
        case (ovr_sign_mode)
            ORG_B_SIGN : newSignA = input_buf.rs2[31]; // cheating, because we know this will only be used for sgn-injection ops that use rs1 and rs2 only
            INV_A_SIGN : newSignA = ~adderInputA_org[31]; // maybe also used by fnmadd/sub
            INV_B_SIGN : newSignA = ~input_buf.rs2[31];
            XOR_SIGNS : newSignA = input_buf.rs1[31] ^ input_buf.rs2[31];
            default /*ORG_A_SIGN*/ : newSignA = adderInputA_org[31]; // maybe also used by fmadd/sub
        endcase

        if (valid_mul[MUL_STAGES-1] && state_mul[MUL_STAGES-1].op.add_mul_rs3) begin // we already have an fmac in pipeline
            addMode_mulResult = 1;
            start_add_in = 1;
            add_takes_mul = 1;
            will_need_adder = 1;
        end else begin
            addMode_mulResult = 0;
            start_add_in = valid_input && !input_buf.op.mul; // we need add_advance also for logic only. So does not matter whether op instructs to actually add or not
            add_takes_mul = 0;
            will_need_adder = valid_input && input_buf.op.add_rs1_rs2;
        end
    end

    logic addIn_out_taken;
    assign addIn_advance = !valid_add[0] || addIn_out_taken;
    logic valid_for_adder;

    always_ff @(posedge clk) begin
        if (rst) begin
            valid_add[0] <= 0;
            valid_for_adder <= 0;
        end else if (addIn_advance) begin
            valid_add[0] <= start_add_in;
            valid_for_adder <= will_need_adder;
        end
        if (addIn_advance) begin
            adderInputA_r <= adderInputA;
            adderInputB_r <= adderInputB;
            state_add[0] <= addMode_mulResult? state_mul[MUL_STAGES-1] : '{ op: input_buf.op, id: input_id_buf};
        end
    end

    logic add_takes_addIn;
    logic add_out_taken;
    assign add_advance = !valid_add[ADD_STAGES-1] || add_out_taken;
    assign add_takes_addIn = valid_for_adder;

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=1; i < ADD_STAGES; i++)
                valid_add[i] <= 0;
        end else if (add_advance) begin
            valid_add[1] <= valid_for_adder; // only continue if we actually need to add
            for (int i=2; i < ADD_STAGES; i++)
                valid_add[i] <= valid_add[i-1]; // only valid if add was needed
        end
        if (add_advance) begin
            adderResult_r <= adderResult;
            for (int i=1; i < ADD_STAGES; i++)
                state_add[i] <= state_add[i-1];
        end
    end

    f_add add( // 2 cyc 
        .clk(clk),
        .ce(add_advance),
        .X(adderInputA_r),
        .Y(adderInputB_r),
        .R(adderResult)
    );

    flopoco_t result;
    id_t result_id;

    logic final_add, final_mul, final_signMod;
    assign final_mul = valid_mul[MUL_STAGES-1] && state_mul[MUL_STAGES-1].op.add_mul_rs3 == 0;
    assign final_add = valid_add[ADD_STAGES-1];
    assign final_signMod = valid_add[0] && !valid_for_adder; // only signMod result if there was NO other op at all

    logic result_takes_mul, result_takes_add, result_takes_signMod;
    assign mul_out_taken = add_takes_mul || result_takes_mul;
    assign add_out_taken = result_takes_add;
    assign addIn_out_taken = result_takes_signMod || add_takes_addIn;

    always_comb begin
        result_takes_mul = 0;
        result_takes_add = 0;
        result_takes_signMod = 0;

        if (final_add) begin
            result = adderResult_r;
            result_id = state_add[ADD_STAGES-1].id;
            result_takes_add = wb.ack;
        end else if (!final_signMod) begin // mul, but give signMod preference while keeping it default
            result = mulResult_r;
            result_id = state_mul[MUL_STAGES-1].id;
            result_takes_mul = wb.ack;
        end else begin // signMod
            result = adderInputA_r;
            result_id = state_add[0].id;
            result_takes_signMod = wb.ack;
        end
    end

    //WB interface
    ////////////////////////////////////////////////////

    assign wb.rd = result;
    assign wb.done = final_add || final_signMod || final_mul;
    assign wb.id = result_id;

endmodule : fp_mac_unit_sp
