`include "systolic_array_add_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

module sysarr_add (
    /* verilator lint_off UNUSEDSIGNAL */
    input logic clk, nRST,
    /* verilator lint_off UNUSEDSIGNAL */
    systolic_array_add_if.add adder
);
always_comb begin
    adder.add_output= '0;
    adder.add_output = adder.add_input1 + adder.add_input2;
end
   
   
endmodule
