`include "systolic_array_add_if.vh"

module sysarr_add (
    /* verilator lint_off UNUSEDSIGNAL */
    input logic clk, nRST,
    /* verilator lint_off UNUSEDSIGNAL */
    systolic_array_add_if.add adder
);
always_comb begin
    adder.add_ouput= '0;
    if (adder.count == 2)begin
        adder.add_ouput = adder.add_input1 + adder.add_input2;
    end
end
   
   
endmodule
