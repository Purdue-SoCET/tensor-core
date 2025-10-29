`include "systolic_array_OUT_FIFO_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

module sysarr_OUT_FIFO(
    input logic clk, nRST,
    systolic_array_OUT_FIFO_if.OUT_FIFO out_fifo
);
    // Internal storage for FIFO
    logic [DW * N - 1 : 0] fifo_mem; 
    logic [DW * N - 1 : 0] fifo_mem_next;

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
            fifo_mem_next = {out_fifo.shift_value, fifo_mem[DW * N - 1: DW]};    // Shift values forward 
        end
    end

endmodule
