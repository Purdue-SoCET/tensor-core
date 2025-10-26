`include "systolic_array_MAC_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

// MAC unit with vaddsubmyles integration
// Modified by: Myles
// Date: October 2025

/* verilator lint_off UNUSEDSIGNAL */
/* verilator lint_off UNUSEDPARAM */

`include "systolic_array_MAC_if.vh"
`timescale 1ns/1ps

module sysarr_MAC_myles(input logic clk, input logic nRST, systolic_array_MAC_if.MAC mac_if);
    logic [DW-1:0] input_x;
    logic [DW-1:0] nxt_input_x;

    logic [DW-1:0] weight, nxt_weight, latched_weight_passon, nxt_latched_weight_passon;
    logic next_weight_next_en;
    assign mac_if.in_pass = mac_if.weight_next_en ? latched_weight_passon : input_x;

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
    logic start_passthrough_1, start_passthrough_2, start_passthrough_3;
    logic run;

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            run_latched <= 1'b0;
        end
        else begin
            run_latched <= (run_latched | mac_if.start) & ~start_passthrough_3;
        end
    end

    assign run = run_latched | mac_if.start;
    assign mac_if.value_ready = ~run;

    // phase 1: multiply
    
    // Signals connecting mul stage1 with stage2
    logic [5:0] mul_fp1_head_s2_in, mul_fp2_head_s2_in;
    logic mul_carryout_in;
    logic [12:0] mul_product_in;
    logic mul_round_loss_s2;
    logic mul_carryout_out;
    logic [12:0] mul_product_out;
    logic mul_round_loss_s1_out;

    // Logic to determine the implicit leading bit of FP mantissa
    logic frac_leading_bit_fp1;
    logic frac_leading_bit_fp2;
    always_comb begin
        if(input_x[14:10] == 5'b0)
            frac_leading_bit_fp1 = 1'b0;
        else
            frac_leading_bit_fp1 = 1'b1;

        if(weight[14:10] == 5'b0)
            frac_leading_bit_fp2 = 1'b0;
        else
            frac_leading_bit_fp2 = 1'b1;
    end

    logic mul_ready, mul_stall;
    mul_wallacetree wallaca (
        .clk(clk),
        .nRST(nRST),
        .active(mac_if.start),
        .a({frac_leading_bit_fp1, input_x[9:0]}),
        .b({frac_leading_bit_fp2, weight[9:0]}),
        .result(mul_product_out),
        .overflow(mul_carryout_out),
        .round_loss(mul_round_loss_s1_out),
        .value_ready(mul_ready)
    );
    assign mul_stall = ~mul_ready;

    // Latching the run signal an extra time to fix timing issue
    logic start_passthrough_0;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)
            start_passthrough_0 <= 0;
        else
            start_passthrough_0 <= mac_if.start | (start_passthrough_0 & mul_stall);
    end

    // Flipflop to connect mul stage1 and stage 2
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

    // Mul stage2: Add exponents
    logic mul_sign_result;
    logic [4:0] mul_sum_exp;
    logic mul_ovf, mul_unf;

    adder_5b add_EXPs (
        .carry(mul_carryout_in),
        .exp1 (mul_fp1_head_s2_in[4:0]),
        .exp2 (mul_fp2_head_s2_in[4:0]),
        .sum  (mul_sum_exp),
        .ovf  (mul_ovf),
        .unf  (mul_unf)
    );
    assign mul_sign_result = mul_fp1_head_s2_in[5] ^ mul_fp2_head_s2_in[5];

    // Final multiplication result
    logic [15:0] mul_result;
    logic [11:0] mul_frac_product;
    assign mul_frac_product = mul_carryout_in ? mul_product_in[12:1] : mul_product_in[11:0];

    // Rounding
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

    // Latch mul_result to reduce critical path
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

    // accumulate using new adder (vaddsubmyles)
    
    logic [15:0] vaddsub_out;
    logic vaddsub_ovf;
    logic vaddsub_enable;
    
    // Enable vaddsub when multiply is complete
    assign vaddsub_enable = start_passthrough_2a & run;
    
    vaddsubmyles vadd_inst (
        .CLK(clk),
        .nRST(nRST),
        .enable(vaddsub_enable),
        .port_a(mul_result_latched),
        .port_b(in_accumulate_latched),
        .out(vaddsub_out),
        .overflow(vaddsub_ovf)
    );

    // pipeline delay to match vaddsub's 2-cycle latency
    logic start_passthrough_2b;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)
            start_passthrough_2b <= 0;
        else if(run)
            start_passthrough_2b <= start_passthrough_2a;
        else
            start_passthrough_2b <= start_passthrough_2b;
    end

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)
            start_passthrough_2 <= 0;
        else if(run)
            start_passthrough_2 <= start_passthrough_2b;
        else
            start_passthrough_2 <= start_passthrough_2;
    end

    // Final stage delay
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)
            start_passthrough_3 <= 0;
        else if(run)
            start_passthrough_3 <= start_passthrough_2;
        else
            start_passthrough_3 <= start_passthrough_3;
    end

    // Output assignment - check for overflow
    assign mac_if.out_accumulate = vaddsub_ovf ? 16'b0111110000000000 : vaddsub_out;

endmodule
