`timescale 1ns/1ps
// need to add description

module mul_fp16_2cycle(input logic clk, input logic nRST, input logic start, input logic [15:0] a, b, output logic [15:0] result, output logic done);

    logic lat1_ready, lat2_ready;               // Signals to denote when the value is ready at each stage of the multiply unit pipeline.
    assign done = lat2_ready;                   // Mul result is ready when the second register is ready - everything downstream of that is combinational.
    // Register 1: Latches input values.
    // Register 2: Latches mantissa multiplication output before going into exponent addition logic.

    // Register 1: latch input values.
    logic [15:0] a_latched, b_latched;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            a_latched <= 0;
            b_latched <= 0;
            lat1_ready <= 0;
        end
        else begin
            a_latched <= a_latched;
            b_latched <= b_latched;
            lat1_ready <= 0;

            if(start == 1'b1) begin
                a_latched <= a;
                b_latched <= b;
                lat1_ready <= 1;
            end
        end
    end

    // Step 1: Multiply mantissa bits.

    // Step 1.1: determine the "implilcit" leading bit of FP mantissa section prior to feeding it through multiplier
    // If the exponent bits are zero, the implicit bit is 0, else its 1.

    logic frac_leading_bit_fp1;
    logic frac_leading_bit_fp2;
    always_comb begin
        if(a_latched[14:10] == 5'b0)begin
            frac_leading_bit_fp1 = 1'b0;
        end
        else begin
            frac_leading_bit_fp1 = 1'b1;
        end

        if(b_latched[14:10] == 5'b0)begin
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

    mul_wallacetree_singlecycle wallaca (
        .a({frac_leading_bit_fp1, a_latched[9:0]}),
        .b({frac_leading_bit_fp2, b_latched[9:0]}),
        .result(mul_product),
        .overflow(mul_carryout),
        .round_loss(mul_round_loss)
    );

    // mul_wallacetree wallaca (
    //     .clk(clk),
    //     .nRST(nRST),
    //     .active(lat1_ready),
    //     .a({frac_leading_bit_fp1, a_latched[9:0]}),
    //     .b({frac_leading_bit_fp2, b_latched[9:0]}),
    //     .result(mul_product),
    //     .overflow(mul_carryout),
    //     .round_loss(mul_round_loss),
    //     .value_ready(mul_ready)
    // );

    // The multiplier taking two cycles means that the result, overflow and round loss bits will be ready two cycles after lat1_ready is asserted.
    // Which means that the remaining data required for step2 (the exponent bits) must be registered an extra time, to keep timing synchronized.
    // Note that since this is hard coded, if the binary multiplier time changes, this sync'ing will have to be updated accordingly.
    // "Head" refers to the first 6 bits of FP16 value, the sign and exponent bits.
    // logic [5:0] a_head_synced, b_head_synced;       // These are the signals that will be used in step2.
    // logic sync_lat_ready;                           // if all is working correctly, this should always match mul_ready.
    // always_ff @(posedge clk, negedge nRST) begin
    //     if(nRST == 1'b0) begin
    //         a_head_synced <= 6'b0;
    //         b_head_synced <= 6'b0;
    //         sync_lat_ready <= 0;
    //     end
    //     else begin
    //         a_head_synced <= a_head_synced;
    //         b_head_synced <= b_head_synced;
    //         sync_lat_ready <= 0;
    //         if(lat1_ready) begin
    //             a_head_synced <= a_latched[15:10];
    //             b_head_synced <= b_latched[15:10];
    //             sync_lat_ready <= 1;
    //         end
    //     end
    // end

    // bypass above latch for singlecycle wallace tree
    logic [5:0] a_head_synced, b_head_synced;
    // logic sync_lat_ready;
    assign a_head_synced = a_latched[15:10];
    assign b_head_synced = b_latched[15:10];
    // assign sync_lat_ready = lat1_ready;


    // Register latching all outputs from mantissa multiplication stage ahead of exponent addition stage.
    // "Register 2".
    logic [5:0] a_head_step2, b_head_step2;
    logic [12:0] mul_product_step2;
    logic mul_round_loss_s2, mul_carryout_s2;

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            a_head_step2 <= 6'b0;
            b_head_step2 <= 6'b0;
            mul_product_step2 <= 13'b0;
            mul_round_loss_s2 <= 0;
            mul_carryout_s2 <= 0;
            lat2_ready <= 0;
        end
        else begin
            a_head_step2 <= a_head_step2;
            b_head_step2 <= b_head_step2;
            mul_product_step2 <= mul_product_step2;
            mul_round_loss_s2 <= mul_round_loss_s2;
            mul_carryout_s2 <= mul_carryout_s2;
            lat2_ready <= 0;
            if(lat1_ready) begin
                a_head_step2 <= a_head_synced;
                b_head_step2 <= b_head_synced;
                mul_product_step2 <= mul_product;
                mul_carryout_s2 <= mul_carryout;
                mul_round_loss_s2 <= mul_round_loss;
                lat2_ready <= 1;
            end
        end
    end

    // Step 2: Exponent addition, result rounding. All combinational, result is ready in this cycle.
    
    // step 2.1: calculate sign of result. Simple XOR
    logic mul_sign_result;
    assign mul_sign_result = a_head_step2[5] ^ b_head_step2[5];

    // Step 2.2: Add exponent bits, taking into account overflow from mantissa multiplication
    logic [4:0] exp_sum;
    logic mul_ovf, mul_unf;
    adder_5b add_EXPs (
        .carry(mul_carryout_s2),
        .exp1 (a_head_step2[4:0]),
        .exp2 (b_head_step2[4:0]),
        .sum  (exp_sum),
        .ovf  (mul_ovf),
        .unf  (mul_unf)
    );

    // Step 2.3: Shift multiply product bits if an overflow occurred during mantissa multiplication (exponent was incremented, now divide mantissa by 2 to match)
    logic [15:0] mul_result;            // this variable will hold the final multiplication result
    logic [11:0] mul_frac_product;
    assign mul_frac_product = mul_carryout_s2 ? mul_product_step2[12:1] : mul_product_step2[11:0];

    // Step 2.4: Rounding.
    // this logic could potentially result in an edge case where if the mul significand is all 1's, rounding will cause it to become 0
    logic [9:0] mul_significand_rounded;
    always_comb begin
        if(mul_frac_product[1] & (mul_frac_product[0] | mul_round_loss_s2 | mul_frac_product[2]))
            mul_significand_rounded = mul_frac_product[11:2] + 1;
        else
            mul_significand_rounded = mul_frac_product[11:2];
    end

    // Concatenation to produce final result.
    logic [4:0] mul_final_exp;
    assign mul_final_exp = (mul_product_step2 == 0) ? 0 : exp_sum;
    assign result = {mul_sign_result, mul_final_exp, mul_significand_rounded};

endmodule
