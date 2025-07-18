// Quick and dirty unsigned integer multiplier, based on logic from Tim Rogers' ECE 362 lecture. Takes n cycles to do an n bit multiplication
// Needs external counter.

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
