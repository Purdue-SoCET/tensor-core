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

module sysarr_MAC(input logic clk, input logic nRST, systolic_array_MAC_if.MAC mac_if);
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
    // always_ff @(posedge clk, negedge nRST) begin
    //     if(nRST == 1'b0)
    //         mac_if.value_ready <= 1'b0;
    //     else
    //         mac_if.value_ready <= mac_if.value_ready ? 0 : ~run;
    // end

    // assign mac_if.value_ready = ~run;

    // phase 1: multiply

    // signals connecting mul stage1 with stage2. these are registered, so need 2 signals (one coming out of stage1 going into register, the other coming out of register going into stage2)
    // Latching the sign and exponent bits of both input values for stage2 of multiplication
    logic [5:0] mul_fp1_head_s1_out, mul_fp1_head_s2_in;
    logic [5:0] mul_fp2_head_s1_out, mul_fp2_head_s2_in;

    logic mul_sign1_out, mul_sign2_out, mul_carryout_out;
    logic mul_sign1_in, mul_sign2_in, mul_carryout_in;
    logic [4:0] mul_exp1_out, mul_exp2_out;
    logic [4:0] mul_exp1_in, mul_exp2_in;
    logic [12:0] mul_product_out;
    logic [12:0] mul_product_in;
    logic mul_round_loss_s1_out, mul_round_loss_s2;

    // assign mac_if.weight_read = weight;
    // assign mac_if.mul_result_read = mul_result_latched;

    // MUL takes in latched input_x from above
    // MUL_step1 is special in that contains a sequential multiplier. This means that other operations need to wait until it finishes, the MAC unit must not move to the next stage after just one clock cycle.
    // It also means that it needs an enable signal. This can be on for one or more clock cycles, I dont think it matters.
    // Since it is the very first thing in the MAC chain, i'm using mac_if.start as this enable signal.
    // The flipflop after this should hold its values, and NOT allow the start passthrough signal to advance until the the multiply finishes (mul_stall goes low)
    logic mul_stall;
    MUL_step1 mul1 (clk, nRST, mac_if.start, input_x, weight, mul_product_out, mul_carryout_out, mul_round_loss_s1_out, mul_stall);
    
    // latching the run signal an extra time to fix a timing issue with mul_stall and mac_if.start
    logic start_passthrough_0;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)
            start_passthrough_0 <= 0;
        else
            start_passthrough_0 <= mac_if.start | (start_passthrough_0 & mul_stall);
    end

    // flipflop to connect mul stage1 and stage 2
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            mul_fp1_head_s2_in <= 0;
            mul_fp2_head_s2_in <= 0;
            mul_carryout_in <= 0;
            mul_product_in <= 0;
            start_passthrough_1 <= 0;
            mul_round_loss_s2 <= 0;
        end
        else if(run) begin
            if(mul_stall)
                start_passthrough_1 <= 0;
            else
                start_passthrough_1 <= start_passthrough_0;
            mul_fp1_head_s2_in <= input_x[15:10];
            mul_fp2_head_s2_in <= weight[15:10];
            mul_carryout_in <= mul_carryout_out;
            mul_product_in  <= mul_product_out;
            // start_passthrough_1 <= mac_if.start;
            mul_round_loss_s2 <= mul_round_loss_s1_out;
        end
        else begin
            mul_fp1_head_s2_in <= mul_fp1_head_s2_in;
            mul_fp2_head_s2_in <= mul_fp2_head_s2_in;
            mul_carryout_in <= mul_carryout_in;
            mul_product_in  <= mul_product_in;
            start_passthrough_1 <= start_passthrough_1;
            mul_round_loss_s2 <= mul_round_loss_s2;
        end
    end

    // signals coming out of mul stage2
    logic mul_sign_result;
    logic [4:0] mul_sum_exp;
    logic mul_ovf, mul_unf;

    // step2 of FP multiply: Add exponents. 
    adder_5b add_EXPs (
        .carry(mul_carryout_in),
        .exp1 (mul_fp1_head_s2_in[4:0]),
        .exp2 (mul_fp2_head_s2_in[4:0]),
        .sum  (mul_sum_exp),
        .ovf  (mul_ovf),
        .unf  (mul_unf)
    );
    assign mul_sign_result = mul_fp1_head_s2_in[5] ^ mul_fp2_head_s2_in[5];

    // goodbye stupid module that just called an adder
    // MUL_step2 mul2 (mul_sign1_in, mul_sign2_in, mul_exp1_in, mul_exp2_in, mul_sign_result, mul_sum_exp, mul_ovf, mul_unf, mul_carryout_in);

    //final multiplication result
    logic [15:0] mul_result;
    logic [11:0] mul_frac_product;
    assign mul_frac_product = mul_carryout_in ? mul_product_in[12:1] : mul_product_in[11:0];

    // this could potentially result in an edge case where if the mul significand is all 1's, rounding will cause it to become 0
    logic [9:0] mul_significand_rounded;
    always_comb begin
        if(mul_frac_product[1] & (mul_frac_product[0] | mul_round_loss_s2 | mul_frac_product[2]))
            mul_significand_rounded = mul_frac_product[11:2] + 1;
        else
            mul_significand_rounded = mul_frac_product[11:2];
    end

    logic [4:0] mul_final_exp;
    assign mul_final_exp = (mul_product_in == 0) ? 0 : mul_sum_exp;
    assign mul_result = {mul_sign_result, mul_final_exp, mul_significand_rounded};


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
            start_passthrough_2a <= start_passthrough_1;
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
