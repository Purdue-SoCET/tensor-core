//By            : Joe Nasti
//Last Updated  : 7/23/18

// modified 11/2024: converted to 16 bit FP multiplier for TPU Systolic Array --Vinay Pundith


//
//Module Summary:
//    First step of multiplication in three-step pipeline.
//    multiplies fraction from fp16 value - padded to 13 bits
//
//Inputs:
//    fp1/2     - single precision floating points
//Outputs:
//    sign1/2   - signs of floating points
//    exp1/2    - exponents of floating points
//    product   - result of fraction multiplication
//    carry_out - signal if there is a carry out of the multiplication

`timescale 1ns/1ps
/* verilator lint_off UNUSEDSIGNAL */

module MUL_step1 (
    input clk, nRST, active,
    input [15:0] fp1_in,
    input [15:0] fp2_in,
    output [12:0] product,
    output carry_out,
    output round_loss,
    output mul_stall
);

    logic frac_leading_bit_fp1;
    logic frac_leading_bit_fp2;
    always_comb begin
        if(fp1_in[14:10] == 5'b0)begin
            frac_leading_bit_fp1 = 1'b0;
        end
        else begin
            frac_leading_bit_fp1 = 1'b1;
        end

        if(fp2_in[14:10] == 5'b0)begin
            frac_leading_bit_fp2 = 1'b0;
        end
        else begin
            frac_leading_bit_fp2 = 1'b1;
        end
    end
    
    // // Counter to drive multicycle multiplier
    // logic [3:0] count;
    // logic mul_start;
    // logic mul_stop;
    // always_ff @(posedge clk, negedge nRST) begin
    //     if(nRST == 1'b0) begin
    //         count <= 0;
    //         mul_start <= 0;
    //     end
    //     else begin
    //         mul_start <= 0;
    //         if(count == 12) begin      
    //             count <= 0;
    //         end
    //         else if(count == 0) begin
    //             if(active == 1'b1) begin
    //                 count <= count + 1;
    //                 mul_start <= 1;
    //             end
    //         end
    //         else begin
    //             count <= count + 1;
    //             // mul_start <= 0;
    //         end
    //     end
    // end

    // assign mul_start = active & (count == 1);
    assign mul_stop = (count == 0); 
    assign mul_stall = |count;

    logic [10:0] op1;
    logic [10:0] op2;
    assign op1 = {frac_leading_bit_fp1, fp1_in[9:0]};
    assign op2 = {frac_leading_bit_fp2, fp2_in[9:0]};

    mul_wallacetree wallaca (
        .clk(clk),
        .nRST(nRST),
        .active(active),
        .a(op1),
        .b(op2),
        .result(result),
        .overflow(carry_out),
        .round_loss(round_loss)
    );

    // mul_multicycle MUL(
    //     .clk(clk),
    //     .nRST(nRST),
    //     .start(mul_start),
    //     .stop(mul_stop),
    //     .op1(op1),
    //     .op2(op2),
    //     .result(product),
    //     .overflow(carry_out),
    //     .round_loss(round_loss)
    // );

endmodule  // MUL_step1
