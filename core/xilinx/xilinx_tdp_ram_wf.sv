/*
 * True Dual Port Block Ram with WRITE_FIRST mode with line-wide WEs
 */

module xilinx_tdp_ram_wf #(
    parameter C_DATA_WIDTH=32,
    parameter C_DEPTH=512
)(
    // Global signals
    input logic clk,

    // Port A (read only)
    input logic en_a,
    input logic we_a,
    input logic[$clog2(C_DEPTH)-1:0] addr_a,
    input logic[C_DATA_WIDTH-1:0] data_in_a,
    output logic[C_DATA_WIDTH-1:0] data_out_a,

    // Port B (read and write)
    input logic en_b,
    input logic we_b,
    input logic[$clog2(C_DEPTH)-1:0] addr_b,
    input logic[C_DATA_WIDTH-1:0] data_in_b,
    output logic[C_DATA_WIDTH-1:0] data_out_b
);
    (* ram_style = "block" *) logic [C_DATA_WIDTH-1:0] ram [C_DEPTH-1:0];

    //implementation
    ////////////////////////////////////////////////////

    initial begin
        for (int i = 0; i < C_DEPTH; i++)
            ram[i] = '0;
    end

    // Port A
    always_ff @(posedge clk) begin
        if (en_a) begin
            if(we_a) begin
                ram[addr_a] <= data_in_a;
                data_out_a <= data_in_a;
            end else begin
                data_out_a <= ram[addr_a];
            end
        end
    end


    // Port B
    always_ff @(posedge clk) begin
        if (en_b) begin
            if(we_b) begin
                ram[addr_b] <= data_in_b;
                data_out_b <= data_in_b;
            end else begin
                data_out_b <= ram[addr_b];
            end
        end
    end

    ////////////////////////////////////////////////////
    //End of Implementation
    ////////////////////////////////////////////////////

    ////////////////////////////////////////////////////
    //Assertions

    ////////////////////////////////////////////////////
    //Trace Interface

endmodule
