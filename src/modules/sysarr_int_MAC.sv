`include "systolic_array_MAC_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

module sysarr_MAC(
    /* verilator lint_off UNUSEDSIGNAL */
    input logic clk, nRST,
    /* verilator lint_off UNUSEDSIGNAL */
    systolic_array_MAC_if.MAC mac
);
    logic [DW-1:0] input_x;
    logic [DW-1:0] nxt_input_x;
    assign mac.in_pass = input_x;

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            input_x <= '0;
        end else begin
            input_x <= nxt_input_x;
        end 
    end
    always_comb begin
        nxt_input_x = input_x;
        if (mac.MAC_shift)begin
            nxt_input_x = mac.in_value;
        end
    end
   always_comb begin
    mac.out_accumulate = '0;
    if (mac.count == ADD_LEN+MUL_LEN-1)begin
        mac.out_accumulate = (input_x * mac.weight) + mac.in_accumulate;
    end
end
endmodule
