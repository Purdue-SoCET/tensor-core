`timescale 1ns/1ps

// This module probably CANNOT handle subtraction!

module add_fp16(input logic clk, nRST, start,
                input logic [15:0] fp1_in, fp2_in,
                output logic [15:0] fp_out );
                // output logic ovf, unf, output_ready);




// step 1: Compare exponents to determine which mantissa to shift for normalization.
logic [4:0] smaller_exponent;
logic [4:0] larger_exponent;
logic exp_select;

// i hope the case where the two exponents are equal isn't an issue?
always_comb begin
    if(fp1_in[14:10] < fp2_in[14:10]) begin     // fp2 has a bigger exponent.
        smaller_exponent = fp1_in[14:10];
        larger_exponent = fp2_in[14:10];
        exp_select = 1'b0;
    end
    else begin                                  // fp1 has a bigger exponent.
        smaller_exponent = fp2_in[14:10];
        larger_exponent = fp1_in[14:10];
        exp_select = 1'b1;
    end
end


// step 2: Handle implicit mantissa bit for value == 0 case
    logic frac_leading_bit_fp1;
    logic frac_leading_bit_fp2;
    always_comb begin
        if(fp1_in[14:10] == 5'b0)
            frac_leading_bit_fp1 = 1'b0;
        else
            frac_leading_bit_fp1 = 1'b1;

        if(fp2_in[14:10] == 5'b0)
            frac_leading_bit_fp2 = 1'b0;
        else
            frac_leading_bit_fp2 = 1'b1;
    end

// step 3: Mantissa normalization. Shift the mantissa of the number with a smaller exponent to the right, by whatever the difference in exponents was.
// aka, divide the mantissa so you can increase the exponent to match the larger one.
logic [4:0] exp_diff, exp_max;
logic [12:0] frac_shifted, frac_not_shifted;
logic sign_shifted, sign_not_shifted;

always_comb begin
    exp_diff = larger_exponent - smaller_exponent;

    if(exp_select == 0) begin                       // fp2 had a bigger exponent: shift fp1.

        // Mantissa is only 13 bits (after appending two zeros and an implcit 1/0). If for normalization you have to shift by more than 13 bits, it's going to be zero.
        // So, i think i can make a shifter that only shifts by the lower 4 bits of exp_diff, and if we had to shift by more than that, just hard code a zero as the output.
        // QUESTION: does this mean i need to turn on an underflow flag?

        if(exp_diff[4]) begin
            frac_shifted = 13'b0;
        end
        else begin
            frac_shifted = {frac_leading_bit_fp1, fp1_in[9:0], 2'b00} >> exp_diff[3:0];
        end
        // rounding_loss = |({frac_leading_bit_fp1, floating_point1_in[9:0], 2'b00} & ((1 << unsigned_exp_diff) - 1));    // chatgpt gave me this
        sign_shifted = fp1_in[15];
        frac_not_shifted = {frac_leading_bit_fp2, fp2_in[9:0], 2'b00};
        sign_not_shifted = fp2_in[15];
        exp_max = fp2_in[14:10];
    end

    else begin                                      // fp1 had a bigger exponent: shift fp2.
        if(exp_diff[4]) begin
            frac_shifted = 13'b0;
        end
        else begin
            frac_shifted = {frac_leading_bit_fp2, fp2_in[9:0], 2'b00} >> exp_diff[3:0];
        end
        // rounding_loss = |({frac_leading_bit_fp2, floating_point2_in[9:0], 2'b00} & ((1 << unsigned_exp_diff) - 1));
        sign_shifted = fp2_in[15];
        frac_not_shifted = {frac_leading_bit_fp1, fp1_in[9:0], 2'b00};
        sign_not_shifted = fp1_in[15];
        exp_max = fp1_in[14:10];
    end
end

// step 4: Add mantissae.

// find which mantissa is bigger
logic [12:0] smaller_mantissa, larger_mantissa;
logic [13:0] mantissa_sum;
logic larger_mantissa_sign;
logic result_sign, signs_differ, mantissa_overflow;

always_comb begin
    if(frac_shifted > frac_not_shifted) begin       // if the mantissae are equal, it doesnt matter what gets selected
        smaller_mantissa = frac_not_shifted;
        larger_mantissa = frac_shifted;
        larger_mantissa_sign = sign_shifted;
    end
    else begin
        smaller_mantissa = frac_shifted;
        larger_mantissa = frac_not_shifted;
        larger_mantissa_sign = sign_not_shifted;
    end

    signs_differ = sign_shifted ^ sign_not_shifted;
end

// register values here, before addition
logic[12:0] smaller_mantissa_l, larger_mantissa_l;
logic larger_mantissa_sign_l, sign_shifted_l, sign_not_shifted_l, signs_differ_l;
logic[4:0] exp_max_l;


always_ff @(posedge clk, negedge nRST) begin
    if(nRST == 1'b0) begin
        smaller_mantissa_l <= 0;
        larger_mantissa_l <= 0;
        exp_max_l <= 0;
        larger_mantissa_sign_l <= 0;
        signs_differ_l <= 0;
        sign_shifted_l <= 0;
        sign_not_shifted_l <= 0;
    end
    else begin
        smaller_mantissa_l <= smaller_mantissa;
        larger_mantissa_l <= larger_mantissa;
        exp_max_l <= exp_max;
        larger_mantissa_sign_l <= larger_mantissa_sign;
        signs_differ_l <= signs_differ;
        sign_shifted_l <= sign_shifted;
        sign_not_shifted_l <= sign_not_shifted;
    end
end

always_comb begin
    // logic: If the signs of the input operands are the same, simply add the two together.
    // The sign of the result will be the sign of both the inputs.
    // If one is positive and the other is negative, the result is the larger value minus the smaller value (using absolute value)
    // and the sign will be the sign of the larger operand.
    if(!signs_differ_l) begin
        mantissa_sum = smaller_mantissa_l + larger_mantissa_l;
        result_sign = sign_shifted_l & sign_not_shifted_l;
    end
    else begin
        mantissa_sum = larger_mantissa_l - smaller_mantissa_l;
        result_sign = larger_mantissa_sign_l;
    end

    mantissa_overflow = mantissa_sum[13];
end

// step 5: Re-normalization of mantissa sum.

// screw all of this im gonna use the old inefficient module

// // step 5.1: Calculate the number of leading zeros in the value.
// // implementing leading-zero-detection (LZD) as a tree.
// logic z1, z2, z3;   // Split input into 3 chunks of 4 bits (or 5 for the last one) each, and check each one individually for where the leading zero is.
// assign z1 = |mantissa_sum[12:9];    // highest 1 is in upper 4 bits?
// assign z2 = |mantissa_sum[8:5];     // highest 1 is in the next 4 below?
// assign z3 = |mantissa_sum[4:0];     // or the lowest 4?

// logic[3:0] l1_loc_1, l1_loc_2, l1_loc_3;
// assign l1_loc_1 = (mantissa_sum[12] ? 0 : (mantissa_sum[11] ? 1 : (mantissa_sum[10] ? 2 : (mantissa_sum[9] ? 3 : 2))));
// assign l1_loc_2 = (mantissa_sum[8] ? 0 : (mantissa_sum[7] ? 1 : (mantissa_sum[6] ? 2 : (mantissa_sum[5] ? 3 : 2))));

// always_comb begin
//     if(|mantissa_sum[12:])
// end
logic [12:0] normalized_mantissa_sum;
logic [3:0] norm_shift;
left_shift normalizer(.fraction(mantissa_sum[12:0]), .result(normalized_mantissa_sum), .shifted_amount(norm_shift));



// step 6: Subtract exponents. I forgot why this exists. Transferred out of subtract.sv
logic [5:0] u_exp1, u_exp2;
logic [4:0] u_shifted_amount;
logic [5:0] u_result;
logic [4:0] exp_minus_shift_amount;

always_comb begin
    u_exp1           = {1'b0, exp_max_l};
    u_shifted_amount = {1'b0, norm_shift};
    u_result         = u_exp1 - u_shifted_amount;
end
assign exp_minus_shift_amount = u_result[4:0];
//------------------------------------------------------------------------------------


// step 7: Rounding.
reg [11:0] round_this;
logic [4:0] exp_out;

always_comb begin
    // ovf = 0;
    // unf = 0;
    if (mantissa_overflow == 1) begin
        round_this = mantissa_sum[12:1];            // i forgot why we dont use the normalized sum here
        exp_out    = exp_max_l + 1;
        // if ((exp_max == 5'b11110) && (~unf_in)) ovf = 1;
    end else begin
        round_this = normalized_mantissa_sum[11:0];
        exp_out    = exp_minus_shift_amount;
        // if (({1'b0, exp_max} < {1'b0,norm_shift}) && (~ovf_in)) unf = 1;
    end
end

logic [15:0] round_out;
logic round_flag;               // I added this. --Vinay 1/31/2025. Verilator wouldn't compile without it.

    // Rounding mode used: Round to Nearest, Tie to Even
    logic G;
    logic R;
    assign G = round_this[1];
    assign R = round_this[0];
    logic [9:0] rounded_fraction;
    always_comb begin
        if(G & (R | round_this[2])) begin
            rounded_fraction = round_this[11:2] + 1;
            round_flag = 1;
        end
        else begin
            rounded_fraction = round_this[11:2];
            round_flag = 0;
        end
    end

    assign fp_out = {result_sign, exp_out, rounded_fraction};
    // assign ovf = 0;
    // assign unf = 0;
    // assign output_ready = 1;

endmodule