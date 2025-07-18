`include "systolic_array_FIFO_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

module sysarr_FIFO(
    input logic clk, nRST,
    systolic_array_FIFO_if.FIFO fifo
);
    // Internal storage for FIFO
    logic [DW-1:0] fifo_mem [1:0][N-1:0]; //need space for two arrays 2 rows of matrix rows
    logic [DW-1:0] nxt_fifo_mem [1:0][N-1:0];
    //fifo_mem_nxt[1][n][dw_bit]

    // write pointer
    logic [$clog2(N)-1:0] rd_ptr;
    logic [$clog2(N)-1:0] nxt_rd_ptr;
    logic ld_ptr;
    logic nxt_ld_ptr;
    logic use_ptr;
    logic nxt_use_ptr;

    always_ff @(posedge clk or negedge nRST) begin
        if (!nRST) begin
            fifo_mem <= '{default: '{default: '0}};     // Reset fifo mem to all zeros
            rd_ptr <= '0;
            ld_ptr <= '0;
            use_ptr <= '0;
        end else begin
            fifo_mem <= nxt_fifo_mem;
            rd_ptr <= nxt_rd_ptr;
            ld_ptr <= nxt_ld_ptr;
            use_ptr <= nxt_use_ptr;
        end
    end
    integer i;
    always_comb begin
        nxt_fifo_mem = fifo_mem;
        nxt_rd_ptr = rd_ptr;
        nxt_ld_ptr = ld_ptr;
        nxt_use_ptr = use_ptr;
        fifo.out = fifo_mem[use_ptr][rd_ptr];
        // fifo.load_values [DW*N-1:0]
        if (fifo.load) begin
            for (i = 0; i < N; i++)begin
                nxt_fifo_mem[ld_ptr][i] = fifo.load_values[(N-1-i) * DW +: DW];
            end
            nxt_ld_ptr = !ld_ptr;
        end
        // read ptr would equal N aka we read everything
        /* verilator lint_off WIDTHEXPAND */
        if (fifo.shift && rd_ptr == N-1)begin
        /* verilator lint_off WIDTHEXPAND */
            nxt_use_ptr = !use_ptr;
            nxt_rd_ptr = 0;
        end else if (fifo.shift)begin
            nxt_rd_ptr = rd_ptr + 1;    // Shift values forward 
        end
    end

endmodule
