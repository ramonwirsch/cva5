

module fpu_unit_sp
    import cva5_config::*;
    import riscv_types::*;
    import cva5_types::*;
    (
        input logic clk,
        input logic rst,

        input fpu_inputs_t fpu_inputs,
        unit_issue_interface.unit issue,
        unit_writeback_interface.unit wb
    );


endmodule : fpu_unit_sp