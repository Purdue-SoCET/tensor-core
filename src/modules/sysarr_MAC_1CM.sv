`include "systolic_array_MAC_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

// MAC unit top level file for systolic array. Ties together adder and multiplier.
/* 
Input comes from systolic array IF

MUL_step1
MUL_step2

ADD_step1
ADD_step2
ADD_step3

https://en.wikipedia.org/wiki/Half-precision_floating-point_format
https://www.sciencedirect.com/topics/computer-science/floating-point-addition
https://verilator.org/guide/latest/install.html#git-install
https://www.veripool.org/ftp/verilator_doc.pdf

*/

// To Do
// Add proper overflow handling -- done? 
// Add start and done signals
//
 
// 
/* verilator lint_off UNUSEDSIGNAL */
/* verilator lint_off UNUSEDPARAM */

`include "systolic_array_MAC_if.vh"
`timescale 1ns/1ps

module sysarr_MAC_1CM(input logic clk, input logic nRST, systolic_array_MAC_if.MAC mac_if);
    logic [DW-1:0] input_x;
    logic [DW-1:0] nxt_input_x;

    logic [DW-1:0] weight, nxt_weight, latched_weight_passon, nxt_latched_weight_passon;
    logic next_weight_next_en;
    assign mac_if.in_pass = mac_if.weight_next_en ? latched_weight_passon : input_x;
    // assign mac_if.weight_next_en = mac_if.weight_en;                    // not able to get this to work latched


    // Latching MAC unit input value, to pass it on to the next 
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            input_x <= '0;
            weight <= '0;
            mac_if.weight_next_en <= 0;
            latched_weight_passon <= 0;
        end else begin
            input_x <= nxt_input_x;
            weight <= nxt_weight;
            mac_if.weight_next_en <= next_weight_next_en;
            latched_weight_passon <= nxt_latched_weight_passon;
        end 
    end
    always_comb begin
        nxt_input_x = input_x;
        nxt_weight = weight;
        nxt_latched_weight_passon = latched_weight_passon;
        next_weight_next_en = mac_if.weight_next_en;
        if(mac_if.weight_en) begin
            nxt_weight = mac_if.in_value;
            next_weight_next_en = 1;
            nxt_latched_weight_passon = weight;
        end
        if (mac_if.MAC_shift)begin
            nxt_input_x = mac_if.in_value;
            next_weight_next_en = 0;
        end
    end

    logic run_latched;
    logic start_passthrough_1, start_passthrough_2, start_passthrough_3;    //, start_passthrough_4, start_passthrough_final;
    logic run;

    always_ff @(posedge clk, negedge nRST) begin    // "latching" enable signal
        if(nRST == 1'b0) begin
            run_latched <= 1'b0;
        end
        else begin
            run_latched <= (run_latched | mac_if.start) & ~start_passthrough_3;
        end
    end

    assign run = run_latched | mac_if.start;       // This is to avoid a 1 clock cycle delay between receiving the start signal and actually starting the operation
    assign mac_if.value_ready = ~run;



//-----------------------------------------------------------------------------------------------------------------------------------
// MULTIPLICATION. Copy paste mul_fp16_singlecycle.sv
//-----------------------------------------------------------------------------------------------------------------------------------

    // Step 1: Multiply mantissa bits.

    // Step 1.1: determine the "implilcit" leading bit of FP mantissa section prior to feeding it through multiplier
    // If the exponent bits are zero, the implicit bit is 0, else its 1.

    logic frac_leading_bit_fp1;
    logic frac_leading_bit_fp2;
    always_comb begin
        if(input_x[14:10] == 5'b0)begin
            frac_leading_bit_fp1 = 1'b0;
        end
        else begin
            frac_leading_bit_fp1 = 1'b1;
        end

        if(weight[14:10] == 5'b0)begin
            frac_leading_bit_fp2 = 1'b0;
        end
        else begin
            frac_leading_bit_fp2 = 1'b1;
        end
    end

    // Step 1.2: Multiply mantissae.
    // With a wallace tree multiplier, this takes two clock cycles (contains one latch in it).
    logic mul_ready;
    logic [12:0] mul_product;
    logic mul_carryout;
    logic mul_round_loss;

    wallacetree_11b wallaca (
        .a({frac_leading_bit_fp1, input_x[9:0]}),
        .b({frac_leading_bit_fp2, weight[9:0]}),
        .result(mul_product),
        .overflow(mul_carryout),
        .round_loss(mul_round_loss)
    );

    // Step 2: Exponent addition, result rounding. All combinational, result is ready in this cycle.
    
    // step 2.1: calculate sign of result. Simple XOR
    logic mul_sign_result;
    assign mul_sign_result = input_x[15] ^ weight[15];

    // Step 2.2: Add exponent bits, taking into account overflow from mantissa multiplication
    logic [4:0] exp_sum;
    logic mul_ovf, mul_unf;
    adder_5b add_EXPs (
        .carry(mul_carryout),
        .exp1 (input_x[14:10]),
        .exp2 (weight[14:10]),
        .sum  (exp_sum),
        .ovf  (mul_ovf),
        .unf  (mul_unf)
    );

    // Step 2.3: Shift multiply product bits if an overflow occurred during mantissa multiplication (exponent was incremented, now divide mantissa by 2 to match)
    logic [15:0] mul_result;                // this variable will hold the final multiplication result
    logic [11:0] mul_frac_product;
    assign mul_frac_product = mul_carryout ? mul_product[12:1] : mul_product[11:0];

    // Step 2.4: Rounding.
    // this logic could potentially result in an edge case where if the mul significand is all 1's, rounding will cause it to become 0
    logic [9:0] mul_significand_rounded;
    always_comb begin
        if(mul_frac_product[1] & (mul_frac_product[0] | mul_round_loss | mul_frac_product[2]))
            mul_significand_rounded = mul_frac_product[11:2] + 1;
        else
            mul_significand_rounded = mul_frac_product[11:2];
    end

    // Concatenation to produce final result.
    logic [4:0] mul_final_exp;
    assign mul_final_exp = (mul_product == 0) ? 0 : exp_sum;
    assign mul_result = {mul_sign_result, mul_final_exp, mul_significand_rounded};


//-----------------------------------------------------------------------------------------------------------------------------------
// END MULTIPLICATION
//-----------------------------------------------------------------------------------------------------------------------------------


    // latch mul_result to reduce critical path here
    logic start_passthrough_2a;
    logic [15:0] mul_result_latched;
    logic [15:0] in_accumulate_latched;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            start_passthrough_2a <= 0;
            mul_result_latched <= 0;
	    in_accumulate_latched <= 0;
        end
        else begin
            start_passthrough_2a <= mac_if.start;
            mul_result_latched <= mul_result;
	    in_accumulate_latched <= mac_if.in_accumulate;
        end
    end



    // phase 2: accumulate

    // signals connecting add stage1 with stage2
    logic add_sign_shifted_in, add_sign_not_shifted_in;
    logic add_sign_shifted_out, add_sign_not_shifted_out;
    logic [12:0] frac_shifted_out, frac_not_shifted_out;
    logic [12:0] frac_shifted_in, frac_not_shifted_in;
    logic [4:0] add_exp_max_out, add_exp_max_in;
    // This does not actually go through step 2 but must be latched until step3
    logic add_round_loss_s1_out, add_round_loss_s2_in;

    ADD_step1 add1 (mul_result_latched, in_accumulate_latched, add_sign_shifted_out, frac_shifted_out, add_sign_not_shifted_out, frac_not_shifted_out, add_exp_max_out, add_round_loss_s1_out);

    // flipflop to connect add stage1 and stage2
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            add_sign_shifted_in     <= 0;
            add_sign_not_shifted_in <= 0;
            frac_shifted_in         <= 0;
            frac_not_shifted_in     <= 0;
            add_exp_max_in          <= 0;
            start_passthrough_2 <= 0;
            add_round_loss_s2_in <= 0;
        end
        else if(run) begin
            add_sign_shifted_in     <= add_sign_shifted_out;
            add_sign_not_shifted_in <= add_sign_not_shifted_out;
            frac_shifted_in         <= frac_shifted_out;
            frac_not_shifted_in     <= frac_not_shifted_out;
            add_exp_max_in          <= add_exp_max_out;
            start_passthrough_2 <= start_passthrough_2a;
            add_round_loss_s2_in <= add_round_loss_s1_out; 
        end
        else begin
            add_sign_shifted_in     <= add_sign_shifted_in;
            add_sign_not_shifted_in <= add_sign_not_shifted_in;
            frac_shifted_in         <= frac_shifted_in;
            frac_not_shifted_in     <= frac_not_shifted_in;
            add_exp_max_in          <= add_exp_max_in;
            start_passthrough_2 <= start_passthrough_2;
            add_round_loss_s2_in <= add_round_loss_s2_in; 
        end
    end

    // signals connecting add stage2 with stage3
    logic add_sign_out, add_sign_in;
    logic [12:0] add_sum_out, add_sum_in;
    logic add_carry_out, add_carry_in;
    logic [4:0] add_exp_max_s2_out, add_exp_max_s3_in;
    // This does not actually go through step 2 but must be latched until step3
    logic add_round_loss_s3_in;

    ADD_step2 add2 (frac_shifted_in, add_sign_shifted_in, frac_not_shifted_in, add_sign_not_shifted_in, add_exp_max_in, add_sign_out, add_sum_out, add_carry_out, add_exp_max_s2_out);

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            add_sign_in             <= 0;
            add_sum_in              <= 0;
            add_carry_in            <= 0;
            add_exp_max_s3_in       <= 0;
            start_passthrough_3 <= 0;
            add_round_loss_s3_in <= 0;
        end
        else if(run) begin
            add_sign_in             <= add_sign_out;
            add_sum_in              <= add_sum_out;
            add_carry_in            <= add_carry_out;
            add_exp_max_s3_in       <= add_exp_max_s2_out;
            start_passthrough_3 <= start_passthrough_2;
            add_round_loss_s3_in <= add_round_loss_s2_in;
        end
        else begin
            add_sign_in             <= add_sign_in;
            add_sum_in              <= add_sum_in;
            add_carry_in            <= add_carry_in;
            add_exp_max_s3_in       <= add_exp_max_s3_in;
            start_passthrough_3 <= start_passthrough_3;
            add_round_loss_s3_in <= add_round_loss_s3_in;
        end
    end
//-------------------------------------------------------------------------------------

    // ADD stage3 outputs
    logic [15:0] accumulate_result;
    logic [4:0] add_flags;
    // Rounding mode: truncation. Maybe should pick something else?
    ADD_step3 add3(0, 0, 0, 0, add_exp_max_s3_in, add_sign_in, add_sum_in, add_carry_in, accumulate_result, add_flags, add_round_loss_s3_in);

    // Check for overflow and assign the value to the interface port
    assign mac_if.out_accumulate = add_flags[2] ? 16'b0111110000000000 : accumulate_result;

endmodule


//-------------------------------------------------------------------------------------
// Integer MAC unit for testing
//-------------------------------------------------------------------------------------




// module sysarr_MAC #(
//     parameter DW = 16,
//     parameter MUL_LEN = 2,
//     parameter ADD_LEN = 3
// )(
//     /* verilator lint_off UNUSEDSIGNAL */
//     input logic clk, nRST,
//     /* verilator lint_off UNUSEDSIGNAL */
//     systolic_array_MAC_if.MAC mac
// );
//     logic [DW-1:0] input_x;
//     logic [DW-1:0] nxt_input_x;
//     assign mac.in_pass = input_x;

//     always_ff @(posedge clk, negedge nRST) begin
//         if(nRST == 1'b0)begin
//             input_x <= '0;
//         end else begin
//             input_x <= nxt_input_x;
//         end 
//     end
//     always_comb begin
//         nxt_input_x = input_x;
//         if (mac.MAC_shift)begin
//             nxt_input_x = mac.in_value;
//         end
//     end
//    always_comb begin
//     mac.out_accumulate = '0;
//     if (mac.count == ADD_LEN+MUL_LEN-1)begin
//         mac.out_accumulate = (input_x * mac.weight) + mac.in_accumulate;
//     end
// end
// endmodule
