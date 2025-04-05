//By            : Joe Nasti
//Last updated  : 11/17/2024 - reduced to 16 bit FP values for systolic array
//
//Module summary:
//    First step for addition operation in three-step pipline.
//    Shifts smaller fraction by difference in exponents
//
//Inputs:
//    floating_point1/2_in - single precision floating point values
//Outputs:
//    sign_shifted         - sign of the floating point that gets shifted
//    frac_shifted         - fraction of the floating point that gets shifted
//    sign_not_shifted     - sign of the floating point that does not get shifted
//    frac_not_shifted     - fraction of the floating point that does not get shifted
//    exp_max              - max exponent of the two given floating points

`timescale 1ns/1ps

module ADD_step1 (
    input  logic [15:0] floating_point1_in,
    input  logic [15:0] floating_point2_in,
    output logic sign_shifted,
    output logic [12:0] frac_shifted,
    output logic sign_not_shifted,
    output logic [12:0] frac_not_shifted,
    output logic [4:0] exp_max,
    output logic rounding_loss
);

    reg  [4:0]   unsigned_exp_diff;
    reg    cmp_out;

    // int_compare:
    // if exp1 >= exp2: cmp_out = 0
    // if exp2 > exp1: cmp_out = 1

    //--------------------------------------------------------------------------------------------
    // Comparing exponents (Logic copied over from what used to be int_compare.sv)
    wire [5:0] u_exp1 = {1'b0, floating_point1_in[14:10]};
    wire [5:0] u_exp2 = {1'b0, floating_point2_in[14:10]};
    reg  [5:0] diff;

    assign unsigned_exp_diff = diff[4:0];

    always_comb begin
        diff = u_exp1 - u_exp2;
        case (diff[5])
            1'b0: cmp_out = 1'b0;
            1'b1: begin
                cmp_out = 1'b1;
                diff = -diff;
            end
        endcase
    end
    //--------------------------------------------------------------------------------------------
    // Handling "implicit" 1/0 leading bit for fraction

    logic frac_leading_bit_fp1;
    logic frac_leading_bit_fp2;
    always_comb begin
        if(u_exp1 == 6'b0)
            frac_leading_bit_fp1 = 1'b0;
        else
            frac_leading_bit_fp1 = 1'b1;

        if(u_exp2 == 6'b0)
            frac_leading_bit_fp2 = 1'b0;
        else
            frac_leading_bit_fp2 = 1'b1;
    end

    // need to: right shift significand (fraction) of number with smaller exponent
    // Fraction format: {1'b1, fp_fraction[9:0], 2'b00}

    always_comb begin
        if(cmp_out == 1) begin
            frac_shifted = {frac_leading_bit_fp1, floating_point1_in[9:0], 2'b00} >> unsigned_exp_diff;
            rounding_loss = |({frac_leading_bit_fp1, floating_point1_in[9:0], 2'b00} & ((1 << unsigned_exp_diff) - 1));    // chatgpt gave me this
            sign_shifted = floating_point1_in[15];
            frac_not_shifted = {frac_leading_bit_fp2, floating_point2_in[9:0], 2'b00};
            sign_not_shifted = floating_point2_in[15];
            exp_max = floating_point2_in[14:10];
        end
        else begin
            frac_shifted = {frac_leading_bit_fp2, floating_point2_in[9:0], 2'b00} >> unsigned_exp_diff;
            rounding_loss = |({frac_leading_bit_fp2, floating_point2_in[9:0], 2'b00} & ((1 << unsigned_exp_diff) - 1));
            sign_shifted = floating_point2_in[15];
            frac_not_shifted = {frac_leading_bit_fp1, floating_point1_in[9:0], 2'b00};
            sign_not_shifted = floating_point1_in[15];
            exp_max = floating_point1_in[14:10];
        end
    end

endmodule
