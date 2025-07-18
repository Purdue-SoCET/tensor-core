//By            : Joe Nasti
//Last Updated  : 11/03/2024 by Vinay Pundith - Converted to 5 bit adder for TPU Systolic Array MAC Unit
//
//Module summary:
//    Adds two unsigned 5 bit integers with ofset of 16 and signals if there is an over/underflow
//Inputs:
//    exp1/2 - 5 bit values to be summed
//Outputs:
//    sum    - 5 bit result of addition regardless of ovf/unf
//    ovf    - signal overflow has occurred
//    unf    - signal underflow has occurred

/* verilator lint_off UNUSEDSIGNAL */

`timescale 1ns/1ps

module adder_5b (
    input        carry,
    input  [4:0] exp1,
    input  [4:0] exp2,
    output [4:0] sum,
    output       ovf,
    output       unf
);

    reg [4:0] r_exp1;
    reg [4:0] r_exp2;
    reg [4:0] r_sum;


    always_comb begin
        r_exp1 = exp1 - 5'b10000;
        r_exp2 = exp2 - 5'b10000;
        r_sum  = r_exp1 + r_exp2;
    end

    assign sum = (exp1 + exp2 + {4'b0, carry}) - 5'b01111;  // Changed from 5'b10000. Also added carry, which wasn't used before. add with offset
    assign ovf = r_sum[4] && ~r_exp1[4] && ~r_exp2[4];
    assign unf = ((carry != 1) || (sum != 5'b11111)) && (~r_sum[4] && r_exp1[4] && r_exp2[4]);

endmodule
