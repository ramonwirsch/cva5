module fp_div_sqrt_unit_sp
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    (
        input logic clk,
        input logic rst,

        input fp_div_sqrt_inputs_t inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );

    localparam DIV_STAGES = 10; // includes input and output buffers
    localparam SQRT_STAGES = 8; // includes input and output buffers

    id_t id_input;
    logic valid_input;
    logic valid_div [DIV_STAGES-1];
    logic valid_sqrt [SQRT_STAGES-1];
    id_t id_div [DIV_STAGES-1];
    id_t id_sqrt [SQRT_STAGES-1];
    logic input_sqrt;

    logic advance_input, advance_div, advance_sqrt;
    assign issue.ready = advance_input;

    flopoco_t inputA, inputB;

    assign advance_input = !valid_input || (advance_div && !inputs.sqrt) || (advance_sqrt && inputs.sqrt);

    always_ff @(posedge clk) begin
        if (rst)
            valid_input <= 0;
        else if (advance_input)
            valid_input <= issue.new_request;
        if (advance_input) begin
            input_sqrt <= inputs.sqrt;
            id_input <= issue.id;
            inputA <= inputs.rs1;
            inputB <= inputs.rs2;
        end
    end

    flopoco_t result_div, result_sqrt;
    flopoco_t result_div_r, result_sqrt_r;

    f_div div( // 8 cycles
        .clk(clk),
        .ce(advance_div),
        .X(inputA),
        .Y(inputB),
        .R(result_div)
    );

    f_sqrt sqrt( // 6 cycles to allow 100MHz on Artix 7
        .clk(clk),
        .ce(advance_sqrt),
        .X(inputA),
        .R(result_sqrt)
    );

    logic valid_div_result, valid_sqrt_result;
    assign valid_div_result = valid_div[DIV_STAGES-2];
    assign valid_sqrt_result = valid_sqrt[SQRT_STAGES-2];

    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i=0; i < DIV_STAGES-1; i++) begin
                valid_div[i] <= 0;
            end
        end else if (advance_div) begin
            valid_div[0] <= valid_input && !input_sqrt;
            for (int i=1; i < DIV_STAGES-1; i++) begin
                valid_div[i] <= valid_div[i-1];
            end
        end
        if (advance_div) begin
            id_div[0] <= id_input;
            for (int i=1; i < DIV_STAGES-1; i++) begin
                id_div[i] <= id_div[i-1];
            end
            result_div_r <= result_div;
        end

        if (rst) begin
            for (int i=0; i < SQRT_STAGES-1; i++) begin
                valid_sqrt[i] <= 0;
            end
        end else if (advance_sqrt) begin
            valid_sqrt[0] <= valid_input && input_sqrt;
            for (int i=1; i < SQRT_STAGES-1; i++) begin
                valid_sqrt[i] <= valid_sqrt[i-1];
            end
        end
        if (advance_sqrt) begin
            id_sqrt[0] <= id_input;
            for (int i=1; i < SQRT_STAGES-1; i++) begin
                id_sqrt[i] <= id_sqrt[i-1];
            end
            result_sqrt_r <= result_sqrt;
        end
    end

    logic div_out_taken, sqrt_out_taken;

    assign advance_div = !valid_div_result || div_out_taken;
    assign advance_sqrt = !valid_sqrt_result || sqrt_out_taken;

    logic output_select;
    assign output_select = valid_div_result;
    assign div_out_taken = wb.ack && !output_select;
    assign sqrt_out_taken = wb.ack && output_select;

    //WB interface
    ////////////////////////////////////////////////////

    assign wb.rd = output_select? result_div_r : result_sqrt_r;
    assign wb.done = valid_div_result || valid_sqrt_result;
    assign wb.id = output_select? id_div[DIV_STAGES-2] : id_sqrt[SQRT_STAGES-2];

endmodule : fp_div_sqrt_unit_sp
