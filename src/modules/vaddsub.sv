`include "vector_types.vh"
`include "vector_if.vh"
//need to add a control signal for the subtract module to flip the sign of the second input
module vaddsub(
    input logic CLK, 
    input logic nRST,
    vaddsub_if.vaddsub vaddsubif 
);

// importing vector types package
import vector_pkg::*;

fp16_t fp1, fp2; //declaring the fp16 types

logic sign_r, overflow; //sign bits for the input and output
logic [4:0] exp_a, exp_b, exp_r; //5 bits for the exponent field
// logic [10:0] frac_a, frac_b, frac_r; //assigning 11 bits including the implicit 1
logic [4:0] exp_diff; //exponent difference
// logic [10:0] frac_a_alligned, frac_b_alligned; //alligned fractions
logic [12:0] frac_a_ext, frac_b_ext; 
logic [13:0] frac_sum; // one more for carry-out

assign fp1 = vaddsubif.port_a;
assign fp2 = vaddsubif.port_b;
assign exp_a = fp1.exp;
assign exp_b = fp2.exp;
assign sign_a = fp1.sign;
assign sign_b = vaddsubif.sub ? (~fp2.sign) : fp2.sign;

always_comb begin
    if (vaddsubif.enable) begin
        //exponent normalization
        if (exp_a > exp_b) begin
            exp_diff = exp_a - exp_b;
            exp_r = exp_a;
            frac_a_ext = {1'b1, fp1.frac, 2'b00};
            frac_b_ext = ({1'b1, fp2.frac, 2'b00} >> exp_diff);
        end else begin
            exp_diff = exp_b - exp_a;
            exp_r = exp_b;
            frac_b_ext = {1'b1, fp2.frac, 2'b00};
            frac_a_ext = ({1'b1, fp1.frac, 2'b00} >> exp_diff);
        end    

        //add and subtraction logic
        if (sign_a == sign_b) begin
            frac_sum = frac_a_ext + frac_b_ext;
            sign_r = sign_a;
        end else begin
            if (frac_a_ext >= frac_b_ext) begin
                frac_sum = frac_a_ext - frac_b_ext;
                sign_r = sign_a;
            end else begin
                frac_sum = frac_b_ext - frac_a_ext;
                sign_r = sign_b;
            end
        end

        //normalization
        for (int i = 0; i < 12; i++) begin
            if (frac_sum[13]) begin
                frac_sum = frac_sum >> 1;
                exp_r = exp_r + 1;
            end else if (frac_sum[12] == 0 && exp_r > 0) begin
                frac_sum = frac_sum << 1;
                exp_r = exp_r - 1;
            end
        end
    end
end

//pack results and take only ten bits of the fraction
assign vaddsubif.out = {sign_r, exp_r, frac_sum[11:2]};

endmodule