

module fp_mac_unit_sp
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    #(
        parameter MUL_STAGES = 2, // only internal to MUL & output buffer, so min 1
        parameter ADD_STAGES = 4 // including in buffers (which include sign-mod logic) & outputbuffer, so min 2
    )
    (
        input logic clk,
        input logic rst,

        input fp_mac_inputs_t inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );

    logic input_advance;
    logic mul_advance;
    logic signMod_advance; // stage0 of add
    logic add_advance; // further stages of add
    logic result_advance;

    typedef struct packed {
        fp_mac_op_t op;
        id_t id;
    } stage_state_t;

    logic valid_input;
    fp_mac_inputs_t input_buf;
    id_t input_id_buf;
    
    //     | | |  (input)
    //   input_buf    
    // r1| |r2 | | \r3
    //   mul   | |  |
    //    buf  | |  |
    //    |  \ | |  |
    //    |   sgn-mod  (comb. selects 2 inputs (mul+rs3 / rs1+rs2). Can SignMod first operand, can invert second operand. First operand is also available as buffered result for sgn-ops).
    //    |   bufA bufB
    //    |  /   \  |           
    //    | |   adder  (also subtracts if 2nd operand was inverted above)
    //    | |    buf
    //    | |   /
    //   result (currently combinatorial)
    //     |  (output)


    logic valid_mul [MUL_STAGES];
    stage_state_t state_mul [MUL_STAGES];

    logic valid_add [ADD_STAGES];
    stage_state_t state_add [ADD_STAGES];

	/////////////////////////////// Input Stage

    assign issue.ready = input_advance;
    logic input_out_taken;
    assign input_advance = !valid_input || input_out_taken;

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

    /////////////////////// Mul Stage

    flopoco_t mulResult;
    flopoco_t mulResult_r;

    flopoco_t mul_rs3_buf [MUL_STAGES];

    logic start_mul;
    assign start_mul = valid_input && input_buf.op.mul;
    logic mul_out_taken;
    assign mul_advance = !valid_mul[MUL_STAGES-1] || mul_out_taken;
    logic mul_takes_input;
    assign mul_takes_input = input_buf.op.mul && mul_advance;

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
            mul_rs3_buf[0] <= input_buf.rs3;
            state_mul[0] <= '{ op: input_buf.op, id: input_id_buf};
            for (int i=1; i < MUL_STAGES; i++) begin
                mul_rs3_buf[i] <= mul_rs3_buf[i-1];
                state_mul[i] <= state_mul[i-1];
            end
            mulResult_r <= mulResult;
        end
    end

    FPMul_sp_param #(
        .NUM_STAGES(1)
    ) mul ( // (needs input + output buffers)
        .clk(clk),
        .ce(mul_advance),
        .X(input_buf.rs1),
        .Y(input_buf.rs2),
        .R(mulResult)
    );

    logic final_mul;
	flopoco_t final_mul_result;
	id_t final_mul_id;
	assign final_mul = valid_mul[MUL_STAGES-1] && state_mul[MUL_STAGES-1].op.add_mul_rs3 == 0;
	//assign final_mul_result = mulResult;
	assign final_mul_result = mulResult_r;
    assign final_mul_id = state_mul[MUL_STAGES-1].id;

	//////////////////// SignMod & Add

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
    logic signMod_takes_input;
    //assign signMod_takes_input = !input_buf.op.add_rs1_rs2 && !input_buf.op.mul && result_takes_signMod;
    assign signMod_takes_input = !input_buf.op.mul && signMod_advance;

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

    logic signMod_out_taken;
    assign signMod_advance = !valid_add[0] || signMod_out_taken;
    //assign signMod_advance = add_advance;
    logic valid_for_adder;
    //logic add_takes_input;
    //assign add_takes_input = input_buf.op.add_rs1_rs2 && signMod_advance;

    always_ff @(posedge clk) begin
        if (rst) begin
            valid_add[0] <= 0;
            valid_for_adder <= 0;
        end else if (signMod_advance) begin
            valid_add[0] <= start_add_in;
            valid_for_adder <= will_need_adder;
        end
        if (signMod_advance) begin
            adderInputA_r <= adderInputA;
            adderInputB_r <= adderInputB;
            state_add[0] <= addMode_mulResult? state_mul[MUL_STAGES-1] : '{ op: input_buf.op, id: input_id_buf};
        end
    end

    logic final_signMod;
	flopoco_t final_signMod_result;
	id_t final_signMod_id;
	//assign final_signMod = valid_input && !input_buf.op.mul && !input_buf.op.add_rs1_rs2; // only signMod result if there was NO other op at all
	assign final_signMod = valid_add[0] && !valid_for_adder; // only signMod result if there was NO other op at all
	//assign final_signMod_result = adderInputA;
	assign final_signMod_result = adderInputA_r;
	//assign final_signMod_id = input_id_buf;
	assign final_signMod_id = state_add[0].id;


    logic add_takes_signMod;
    logic add_out_taken;
    assign add_advance = !valid_add[ADD_STAGES-1] || add_out_taken;
    assign add_takes_signMod = valid_for_adder;

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=1; i < ADD_STAGES; i++) // skips stage0. handled separately above, because it is sgn-mod AND adder-input simultaneously
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

    FPAdd_sp_param #(
        .NUM_STAGES(2)
    ) add ( 
        .clk(clk),
        .ce(add_advance),
        .X(adderInputA_r),
        .Y(adderInputB_r),
        .R(adderResult)
    );

    flopoco_t result;
    id_t result_id;

  	logic final_add;
	flopoco_t final_add_result;
	id_t final_add_id;
    assign final_add = valid_add[ADD_STAGES-1];
	//assign final_add_result = adderResult;
	assign final_add_result = adderResult_r;
	assign final_add_id = state_add[ADD_STAGES-1].id;

	/////////////////////// Result Stage

    logic result_takes_mul, result_takes_add, result_takes_signMod;
    assign mul_out_taken = add_takes_mul || result_takes_mul;
    assign add_out_taken = result_takes_add;
    assign signMod_out_taken = result_takes_signMod || add_takes_signMod;
    //assign input_out_taken = mul_takes_input || add_takes_input || signMod_takes_input;
    assign input_out_taken = mul_takes_input || signMod_takes_input;

    flopoco_t shared_result;
    //flopoco_t shared_result_r;
    id_t shared_result_id;
    //id_t shared_result_id_r;
    logic valid_shared_result;
    //logic valid_shared_result_r;

    always_comb begin
        result_takes_mul = 0;
        result_takes_add = 0;
        result_takes_signMod = 0;

        if (final_add) begin
            shared_result = final_add_result;
            shared_result_id = final_add_id;
            result_takes_add = result_advance;
        end else if (!final_signMod) begin // mul, but give signMod preference while keeping it default
            shared_result = final_mul_result;
            shared_result_id = final_mul_id;
            result_takes_mul = result_advance;
        end else begin // signMod
            shared_result = final_signMod_result;
			shared_result_id = final_signMod_id;
            result_takes_signMod = result_advance;
        end
    end

    assign valid_shared_result = final_add || final_signMod || final_mul;

    //assign result_advance = !valid_shared_result_r || wb.ack;
    assign result_advance = wb.ack;

    //always_ff @(posedge clk) begin
    //    if (rst)
    //        valid_shared_result <= 0;
    //    else if (result_advance)
    //        valid_shared_result_r <= valid_shared_result;
    //    if (result_advance) begin
    //        shared_result_r <= shared_result;
    //        shared_result_id_r <= shared_result_id;
    //    end
    //end

    //WB interface
    ////////////////////////////////////////////////////

	// variant with shared result buffer
    //assign wb.rd = shared_result_r;
    //assign wb.done = valid_shared_result;
    //assign wb.id = shared_result_id_r;

    assign wb.rd = shared_result;
	assign wb.done = valid_shared_result;
	assign wb.id = shared_result_id;

endmodule : fp_mac_unit_sp
