/* FU Vector Divide Code */
`include "vdiv_if.vh"

module vdiv
(
    input logic CLK, nRST,
    vdiv_if.div divif
);

// Sequential logic to pulse done for 1 cycle
logic done, next_done, done_pulsed, skip_divider, is_ovf;
assign next_done = (divif.en && skip_divider || done);
always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST) begin
        divif.done <= 0;
        done_pulsed <= 0;
    end else begin
        divif.done <= ~done_pulsed && next_done;
        if (done_pulsed) done_pulsed <= 0;
        else if (next_done) done_pulsed <= 1;
    end
end

// Split FP16 inputs into components
logic sign_a, sign_b;
logic [4:0] exp_a, exp_b;
logic [9:0] mant_a, mant_b;
assign {sign_a, exp_a, mant_a} = divif.a;
assign {sign_b, exp_b, mant_b} = divif.b;

// Compute sign (simple XOR)
logic final_sign;
assign final_sign = sign_a ^ sign_b;

// Check if inputs are special values
logic exp_a_max, exp_b_max;
assign exp_a_max = &exp_a;
assign exp_b_max = &exp_b;
logic a_zero, b_zero, a_inf, b_inf, a_nan, b_nan;
assign a_zero = (exp_a == 0); // Treat subnormals as zero
assign b_zero = (exp_b == 0); // Treat subnormals as zero
assign a_inf = exp_a_max && (mant_a == 0);
assign b_inf = exp_b_max && (mant_b == 0);
assign a_nan = exp_a_max && (mant_a != 0);
assign b_nan = exp_b_max && (mant_b != 0);

// Edge case handling for NaN, infinity, and zero outputs
logic is_nan, is_inf, is_zero;
assign is_nan = a_nan || b_nan || (a_zero && b_zero) || (a_inf && b_inf);
assign is_inf = (!is_nan) && (a_inf || b_zero);
assign is_zero = (!is_nan) && (!is_inf) && (a_zero || b_inf);
assign skip_divider = is_nan || is_inf || is_zero; // skip division if edge case

// Compute raw exponent
logic [5:0] exp;
assign exp = exp_a - exp_b + 15;

// Compute raw quotient
logic [22:0] quotient;
int_divider #(.SIZE(23), .SKIP(11)) divider (
    .CLK(CLK), .nRST(nRST), .en(divif.en && !skip_divider),
    .x({divif.a[14:10] != 0, divif.a[9:0], 12'b0}), .y({12'b0, divif.b[14:10] != 0, divif.b[9:0]}),
    .result(quotient), .done(done)
);
// assign quotient = ({exp_a != 0, mant_a, 12'b0} / {exp_b != 0, mant_b});
// assign done = 1;

// Normalize exponent and quotient, set rounding bit
logic [9:0] mant;
logic round_bit;
logic [5:0] exp_norm;
always_comb begin
    if (exp == 0) begin
        {mant, round_bit} = quotient[12:2];
        exp_norm = exp;
    end else if (exp == 1) begin
        {mant, round_bit} = quotient[11:1];
        exp_norm = quotient[12];
    end else if (quotient[12]) begin
        {mant, round_bit} = quotient[11:1];
        exp_norm = exp;
    end else begin
        {mant, round_bit} = quotient[10:0];
        exp_norm = exp - 1;
    end
end

// Detect overflow (positive exponent minus negative exponent, exp > 30)
assign is_ovf = ~skip_divider & exp_a[4] & ~exp_b[4] & (exp_norm > 30);

// Handle subnormal outputs
logic [5:0] shift_amt;
logic [9:0] shifted_mant;
logic new_round_bit;
logic [9:0] final_mant;
logic [4:0] final_exp;
assign shift_amt = exp_norm[5] ? 1 - exp_norm : 0;
assign {shifted_mant, new_round_bit} = {1'b1, mant, round_bit} >> shift_amt;
assign final_mant = shifted_mant[9:0] + new_round_bit;
assign final_exp = exp_norm[5] ? 0 : exp_norm[4:0];

// Compute final result (accounting for edge cases)
always_comb begin
    if (is_nan)
        divif.result = {final_sign, 5'b11111, 10'h200};
    else if (is_inf || is_ovf && !skip_divider)
        divif.result = {final_sign, 5'b11111, 10'b0};
    else if (is_zero)
        divif.result = {final_sign, 5'b0, 10'b0};
    else
        divif.result = {final_sign, final_exp, final_mant};
end

endmodule