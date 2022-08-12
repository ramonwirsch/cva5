
module instruction_invalidation_queue
    #(
        parameter DEPTH = 4,
        parameter ADDR_WIDTH = 30
    )
    (
        input logic clk,
        input logic rst,

        instruction_invalidation_interface.sink source,
        instruction_invalidation_queued.source sink
    );

    // create fifo interface for invalidation addresses
    fifo_interface #(.DATA_WIDTH(ADDR_WIDTH)) fifo_iface();
    // create fifo for invalidation addresses
    cva5_fifo #(
        .DATA_WIDTH(ADDR_WIDTH),
        .FIFO_DEPTH(DEPTH)
    ) invalidation_fifo (
        .clk(clk),
        .rst(rst),
        .fifo(fifo_iface)
    );

    // enqueue
    assign fifo_iface.push = source.inv_valid;
    assign fifo_iface.potential_push = source.inv_valid;
    assign fifo_iface.data_in = source.inv_addr[ADDR_WIDTH+1:2];

    // dequeue
    assign sink.inv_addr = {{(30-ADDR_WIDTH){1'b0}}, fifo_iface.data_out}; //TODO if we ever want to reduce that width, we probably need a constant for the upper bits, in case they are not 0
    assign sink.inv_valid = fifo_iface.valid;
    assign fifo_iface.pop = sink.inv_completed;

    assign source.inv_ready = ~fifo_iface.full;
    assign source.inv_outstanding = fifo_iface.valid;


endmodule : instruction_invalidation_queue