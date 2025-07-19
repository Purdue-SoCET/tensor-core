// THIS VERSION WILL ONLY WORK IF ADDERS AND MACS HAVE INDIVIDUAL START SIGNALS
// `include "systolic_array_OUT_FIFO_if.vh"
// `include "sys_arr_pkg.vh"
// /* verilator lint_off IMPORTSTAR */
// import sys_arr_pkg::*;
// /* verilator lint_off IMPORTSTAR */

// module sysarr_OUT_FIFO(
//     input logic clk, nRST,
//     systolic_array_OUT_FIFO_if.OUT_FIFO out_fifo
// );
//     // Internal storage for FIFO
//     logic [DW-1:0] fifo_mem [N-1:0];
//     logic [DW-1:0] fifo_mem_nxt [N-1:0];
//     logic [$clog2(N)-1:0] wrt_ptr;
//     logic [$clog2(N)-1:0] wrt_ptr_nxt;

//     always_ff @(posedge clk or negedge nRST) begin
//         if (!nRST) begin
//             fifo_mem <= '{default: '0};     // Reset fifo mem to all zeros
//             wrt_ptr <= '0;
//         end else begin
//             fifo_mem <= fifo_mem_nxt; 
//             wrt_ptr <= wrt_ptr_nxt;
//         end
//     end
//     int i;
//     always_comb begin
//         fifo_mem_nxt = fifo_mem;
//         wrt_ptr_nxt = wrt_ptr;
//         /* verilator lint_off WIDTHEXPAND */
//         if (out_fifo.shift && wrt_ptr == N-1)begin
//         /* verilator lint_off WIDTHEXPAND */
//             fifo_mem_nxt[wrt_ptr] = out_fifo.shift_value;
//             wrt_ptr_nxt = '0;
//         end else if (out_fifo.shift) begin
//             fifo_mem_nxt[wrt_ptr] = out_fifo.shift_value;
//             wrt_ptr_nxt = wrt_ptr + 1;
//         end
//         for (i = 0; i < N; i++) begin
//             out_fifo.out[(i+1)*DW - 1 -: DW] = fifo_mem[N-1-i];
//         end
//     end

// endmodule

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
    logic [DW * N - 1 : 0] fifo_mem_nxt;

    always_ff @(posedge clk or negedge nRST) begin
        if (!nRST) begin
            fifo_mem <= '0;     // Reset fifo mem to all zeros
        end else begin
            fifo_mem <= fifo_mem_nxt; 
        end
    end
    always_comb begin
        fifo_mem_nxt = fifo_mem;
        out_fifo.out = fifo_mem;
        if (out_fifo.shift) begin
            fifo_mem_nxt = {fifo_mem[DW * (N-1) - 1 : 0], out_fifo.shift_value}; 
        end
    end
endmodule
