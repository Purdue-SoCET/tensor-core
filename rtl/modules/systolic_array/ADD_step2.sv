//By            : Joe Nasti
//Last Updated  : 11/17/2024 - Converted to FP16 adder for systolic array MAC unit
//
//Module Summary:
//    Second Step for addition operation in three-step pipeline
//    Adds the fractions with sign bit from ADD_step1
//
//Inputs:
//    frac1/2    - magnitudes of fractions to be added
//    sign1/2    - signs of fractions to be added
//    exp_max_in - max exponent from step1 (if the sum is zero the exponent is set to zero)
//Outputs:
//    sign_out    - sign of the result
//    sum         - magnitude of the result regardless of any carry out
//    carry_out   - signal if there is an oveflow from the addition
//    exp_max_out - if sum is non-zero, this is equal to exp_max_in

/* verilator lint_off UNUSEDSIGNAL */

`timescale 1ns/1ps

module ADD_step2 (
    input      [12:0] frac1,
    input             sign1,
    input      [12:0] frac2,
    input             sign2,
    input      [ 4:0] exp_max_in,  //
    output logic            sign_out,
    output logic     [12:0] sum,
    output logic            carry_out,
    output reg [ 4:0] exp_max_out  //
);

    reg [13:0] frac1_signed;
    reg [13:0] frac2_signed;
    reg [13:0] sum_signed;

    assign exp_max_out = exp_max_in;
    // I have no idea why this existed, it seems to cause an issue where if the sum overflows perfectly the output gets set to 0. --Vinay
    // always_comb begin : exp_max_assignment
    //     if (sum == 0) exp_max_out = 5'b00000;
    //     else exp_max_out = exp_max_in;
    // end

    // always_comb begin
    //     case({sign1, sign2})
    //         2'b00: sum = frac1 + frac2;
    //         2'b01: sum = frac1 - frac2;
    //         2'b10: sum = frac2 - frac1;
    //         2'b11: sum = frac1 + frac2;
    //     endcase
    // end

    u_to_s change_to_signed1 (
        .sign(sign1),
        .frac_unsigned(frac1),
        .frac_signed(frac1_signed)
    );

    u_to_s change_to_signed2 (
        .sign(sign2),
        .frac_unsigned(frac2),
        .frac_signed(frac2_signed)
    );

    adder_13b add_signed_fracs (
        .frac1(frac1_signed),
        .frac2(frac2_signed),
        .sum  (sum_signed),
        .ovf  (carry_out)
    );

    s_to_u change_to_unsigned (
        .frac_signed(sum_signed),
        .sign(sign_out),
        .frac_unsigned(sum)
    );


endmodule

