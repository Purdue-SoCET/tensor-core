// Quick and dirty unsigned integer multiplier, based on logic from Tim Rogers' ECE 362 lecture. Takes n cycles to do an n bit multiplication
// Parameterized to work with any size inputs (as long as both are the same size) - use the num_bits parameter.
// Not pipeline-able because the same set of hardware is re-used in each clock cycle, at no point is there any unused hardware that could be filled with another operation.
// inputs are op1 and op2.
// Needs external counter to time *start* and *stop* input signals.
// Timing: *start* needs to be on for exactly one clock cycle. N cycles (where N is the number of bits in the output)later, the answer *result* will be ready.
//          data in flip-flops (and the result) stay constant as long as *stop* is asserted. if *stop* is asserted after N cycles, it will freeze the correct output on the *result* port. (If the *result* output is not frozen and captured before or after N cycles, the value will be incorrect)
// Multiplying two N bit numbers yeilds an N*2 bit product. This multiplier truncates off the lower N bits, returning only the upper N bits. This is acceptable for floating-point operations because the lower bits only offer more decimal points of accuracy.
// *round_loss* is asserted if any of the lower N bits that were truncated off were 1. This is used for rounding, if any of them were 1, FP rounding logic can decide to round up.
// i forgot how overflow works.
// by: Vinay Pundith (vpundith@purdue.edu / vinaypundith@gmail.com), Spring 2025

`timescale 1ns/1ps

module mul_multicycle #(parameter num_bits = 13) (input logic clk, nRST, start, stop, input logic [num_bits-1:0] op1, op2, output logic [num_bits-1:0] result, output logic overflow, round_loss);

logic [num_bits-1:0] multiplicand, next_multiplicand;
logic [(num_bits*2)-1:0] product, next_product;

assign overflow = product[(num_bits*2)-1];
assign result = product[(num_bits*2-2):num_bits-1];
assign round_loss = |product[num_bits-2:0];

// op2 is the "multiplier", op1 is the "multiplicand"
always_comb begin
    next_multiplicand = multiplicand;
    next_product = product;

    // Capture inputs to start the operation.
    // When the operation begins, fill multiplier into right half of product register
    if(start) begin
        next_product[num_bits-1:0] = op2;
        // next_product[num_bits*2-1:num_bits] = product[num_bits*2-1:num_bits];
        next_multiplicand = op1;
    end

    // Multiplication is complete:
    else if(stop) begin
        next_multiplicand = multiplicand;
        next_product = product;
    end

    // Normal operation:
    else if(product[0] == 1'b1) begin
        // Add multiplicand to left half of product register, and shift right
        next_product[num_bits-2:0] = product[num_bits-1:1];
        next_product[num_bits*2-1:num_bits-1] = product[num_bits*2-1:num_bits] + multiplicand;
    end
    else if(product[0] == 0) begin
        next_product = product >> 1;
    end
end

always_ff @(posedge clk, negedge nRST) begin
    if(nRST == 1'b0) begin
        product <= 0;
        multiplicand <= 0;
    end
    else begin
        product <= next_product;
        multiplicand <= next_multiplicand;
    end
end
endmodule
