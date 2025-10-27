//By            : Joe Nasti
//Last Updated  : 10/27/2025 by Vinay Pundith - Converted to 8 bit adder for TPU Systolic Array BF16 MAC Unit
//
//Module summary:
//    Adds two unsigned 8 bit integers with ofset of 16 and signals if there is an over/underflow
//Inputs:
//    exp1/2 - 8 bit values to be summed
//Outputs:
//    sum    - 8 bit result of addition regardless of ovf/unf
//    ovf    - signal overflow has occurred
//    unf    - signal underflow has occurred

/* verilator lint_off UNUSEDSIGNAL */

`timescale 1ns/1ps

module adder_8b (
    input        carry,
    input  [7:0] exp1,
    input  [7:0] exp2,
    output [7:0] sum,
    output       ovf,
    output       unf
);

    reg [7:0] r_exp1;
    reg [7:0] r_exp2;
    reg [7:0] r_sum;


    always_comb begin
        r_exp1 = exp1 - 8'b10000000;
        r_exp2 = exp2 - 8'b10000000;
        r_sum  = r_exp1 + r_exp2;
    end

    assign sum = (exp1 + exp2 + {7'b0, carry}) - 8'b01111111;  // Changed from 5'b10000. Also added carry, which wasn't used before. add with offset
    assign ovf = r_sum[7] && ~r_exp1[7] && ~r_exp2[7];
    assign unf = ((carry != 1) || (sum != 8'b11111111)) && (~r_sum[7] && r_exp1[7] && r_exp2[7]);

endmodule
