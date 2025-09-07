`include "vector_types.vh"
`include "vector_if.vh"

//need to add a control signal for the subtract module to flip the sign of the second input
module vaddsub(
    input logic CLK, 
    input logic nRST,
    vaddsub_if.vasif vasif 
);

// importing vector types package
import vector_pkg::*;

fp16_t fp1, fp2; //declaring the fp16 types

logic sign_a, sign_b, sign_r, overflow; //sign bits for the input and output
logic [4:0] exp_a, exp_b, exp_r; //5 bits for the exponent field
logic [10:0] frac_a, frac_b, frac_r; //assigning 11 bits including the implicit 1
logic [4:0] exp_diff; //exponent difference
logic [10:0] frac_a_alligned, frac_b_alligned; //alligned fractions

assign sign_a = fp1.sign; //assigning all the signs fo the fp16 values
assign sign_b = fp2.sign;

assign exp_a = fp1.exp; //assigning all the exponents of the fp16 values
assign exp_b = fp2.exp;

assign frac_a = {1'b1, fp1.frac}; //including the implicit 1 in the fraction
assign frac_b = {1'b1, fp2.frac};

assign fp1 = vasif.port_a; //assigning the inputs from the interface to the fp16 types
assing fp2 = vasif.port_b;


assign sign_b = vasif.sub ? ~sign_b : sign_b; //flip the sign of input b if the subtract signal is high

always_comb begin
    if (vasif.enable == 1) begin
        if (exp_a > exp_b) begin //check which exponent is greater
            exp_diff = exp_a - exp_b; //compute the difference
            exp_r = exp_a;
            frac_a_alligned = frac_a; //no need to allign the fraction of the greater exponent
            frac_b_alligned = frac_b >> exp_diff; //shifting the fraction so that both exponents are equal
        end
        else begin
            exp_diff = exp_a - exp_b;
            exp_r = exp_b;
            frac_b_alligned = frac_b;
            frac_a_alligned = frac_a >> exp_diff;
        end
    end
    else begin
        break;
    end
end

//add/subtract the fractions

always_comb begin
    if (vasif.enable == 1) begin
        if (sub) begin
            sign_b = ~sign_b; //flip the sign of the second number
        end
        if (sign_a == sign_b) begin //if the signs are the same, add
            frac_r = frac_a_alligned + frac_b_alligned;
            sign_r = sign_a; //sign of the result stays the same
        end 
        else begin
            if (frac_a_alligned >= frac_b_alligned) begin //if the signs are different and frac_a is greater
                frac_r = frac_a_alligned - frac_b_alligned; //subtract
                sign_r = sign_a; //keep the sign of the greater number
            end else begin
                frac_r = frac_b_alligned - frac_a_alligned; //if the fraction of the second number is greater, subtract the other way
                sign_r = sign_b; //flip the sign
            end
        end
    end
    else begin
        break;
    end
end

//normlization/overflow handling

always_comb begin
    if (vasif.enable == 1) begin
        if (frac_r[10] == 0) begin //normalization
            integer i;
            integer leading_zeros = 0;
            for (i = 0; i < 10; i = i - 1) begin
                if (frac_r[i] == 0) begin
                    leading_zeros++;
                end
            end

            frac_r = frac_r << leading_zeros;
            exp_r = exp_r - leading_zeros;
        end
        else begin //overflow case
            frac_r = frac_r >> 1;
            exp_r = exp_r + 1;
        end
    end
    else begin
        break;
    end
end

//pack the result back into fp16 format

assing out = {sign_r, exp_r, frac_r[9:0]}; //final output

endmodule
