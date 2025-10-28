/* FU Vector Divide Code */
`include "vdiv_if.vh"

module vdiv
(
    input logic CLK, nRST,
    vdiv_if.div divif
);

localparam int EXP_WIDTH = divif.EXP_WIDTH;
localparam int MANT_WIDTH = divif.MANT_WIDTH;

// Sequential logic to pulse done for 1 cycle
logic done, next_done, done_pulsed, skip_divider, is_ovf, is_sub;
assign next_done = (divif.in.en && skip_divider || done);
always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST) begin
        divif.out.done <= 0;
        done_pulsed <= 0;
    end else begin
        divif.out.done <= ~done_pulsed && next_done;
        if (done_pulsed) done_pulsed <= 0;
        else if (next_done) done_pulsed <= 1;
    end
end

// Split FP inputs into components
logic sign_a, sign_b;
logic [EXP_WIDTH-1:0] exp_a, exp_b;
logic [MANT_WIDTH-1:0] mant_a, mant_b;
assign {sign_a, exp_a, mant_a} = divif.in.a;
assign {sign_b, exp_b, mant_b} = divif.in.b;

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
localparam int bias = (1 << (EXP_WIDTH - 1)) - 1;
logic [EXP_WIDTH:0] exp;
assign exp = exp_a - exp_b + bias;

// Compute raw quotient
logic [MANT_WIDTH*2+2:0] quotient;
int_divider #(.SIZE(MANT_WIDTH*2+3), .SKIP(MANT_WIDTH+1)) divider (
    .CLK(CLK), .nRST(nRST), .en(divif.in.en && !skip_divider),
    .x({divif.in.a[MANT_WIDTH+:EXP_WIDTH] != 0, mant_a, {(MANT_WIDTH+2){1'b0}}}),
    .y({{(MANT_WIDTH + 2){1'b0}}, exp_b != 0, mant_b}),
    .result(quotient), .done(done)
);

// Normalize exponent and quotient, set rounding bit
logic [MANT_WIDTH-1:0] mant, final_mant;
logic round_bit;
logic [EXP_WIDTH:0] exp_norm;
logic [EXP_WIDTH-1:0] final_exp;
always_comb begin
    if (exp == 0) begin
        final_mant = quotient[MANT_WIDTH+2:3] + quotient[2];
        exp_norm = exp;
    end else if (exp == 1) begin
        final_mant = quotient[MANT_WIDTH+1:2] + quotient[1];
        exp_norm = quotient[MANT_WIDTH+2];
    end else if (quotient[MANT_WIDTH+2]) begin
        final_mant = quotient[MANT_WIDTH+1:2] + quotient[1];
        exp_norm = exp;
    end else begin
        final_mant = quotient[MANT_WIDTH:1] + quotient[0];
        exp_norm = exp - 1;
    end
end
assign final_exp = exp_norm[EXP_WIDTH-1:0];

// Detect overflow (positive exponent minus negative exponent, exp > 2 ^ EXP_WIDTH - 2)
assign is_ovf = ~skip_divider & exp_a[EXP_WIDTH-1] & ~exp_b[EXP_WIDTH-1] & (exp_norm > (1 << EXP_WIDTH) - 2);
assign is_sub = exp_norm[EXP_WIDTH] || exp_norm == 0;

// Compute final result (accounting for edge cases)
always_comb begin
    if (is_nan)
        divif.out.result = {final_sign, {EXP_WIDTH{1'b1}}, 1'b1, {(MANT_WIDTH-1){1'b0}}};
    else if (is_inf || is_ovf && !skip_divider)
        divif.out.result = {final_sign, {EXP_WIDTH{1'b1}}, {MANT_WIDTH{1'b0}}};
    else if (is_zero || is_sub)
        divif.out.result = {final_sign, {EXP_WIDTH{1'b0}}, {MANT_WIDTH{1'b0}}};
    else
        divif.out.result = {final_sign, final_exp, final_mant};
end

endmodule