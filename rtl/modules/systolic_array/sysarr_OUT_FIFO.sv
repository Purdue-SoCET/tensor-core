`include "systolic_array_OUT_FIFO_if.vh"

module sysarr_OUT_FIFO #(
    parameter N = 4, 
    parameter WIDTH = 16
)(
    input logic clk, nRST,
    systolic_array_OUT_FIFO_if.OUT_FIFO out_fifo
);
    // Internal storage for FIFO
    logic [WIDTH * N - 1 : 0] fifo_mem; 
    logic [WIDTH * N - 1 : 0] fifo_mem_next;

    always_ff @(posedge clk or negedge nRST) begin
        if (!nRST) begin
            fifo_mem <= '0;     // Reset fifo mem to all zeros
        end else begin
            fifo_mem <= fifo_mem_next; 
        end
    end
    always_comb begin
        fifo_mem_next = fifo_mem;
        out_fifo.out = fifo_mem; // Output from the last row
        if (out_fifo.shift) begin
            fifo_mem_next = {out_fifo.shift_value, fifo_mem[WIDTH * N - 1: WIDTH]};    // Shift values forward 
        end
    end

endmodule
