`include "systolic_array_add_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

module sysarr_add (
    /* verilator lint_off UNUSEDSIGNAL */
    input logic clk, nRST,
    /* verilator lint_off UNUSEDSIGNAL */
    systolic_array_add_if.add adder
);

    logic run_latched;
    logic start_passthrough_2, start_passthrough_3;    //, start_passthrough_4, start_passthrough_final;
    logic run;

    always_ff @(posedge clk, negedge nRST) begin    // "latching" enable signal
        if(nRST == 1'b0) begin
            run_latched <= 1'b0;
        end
        else begin
            run_latched <= (run_latched | adder.start) & ~start_passthrough_3;
        end
    end

    assign run = run_latched | adder.start;       // This is to avoid a 1 clock cycle delay between receiving the start signal and actually starting the operation
    assign adder.value_ready = ~run;

    logic add_sign_shifted_in, add_sign_not_shifted_in;
    logic add_sign_shifted_out, add_sign_not_shifted_out;
    logic [12:0] frac_shifted_out, frac_not_shifted_out;
    logic [12:0] frac_shifted_in, frac_not_shifted_in;
    logic [4:0] add_exp_max_out, add_exp_max_in;

    ADD_step1 add1 (adder.add_input1, adder.add_input2, add_sign_shifted_out, frac_shifted_out, add_sign_not_shifted_out, frac_not_shifted_out, add_exp_max_out);

    // flipflop to connect add stage1 and stage2
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            add_sign_shifted_in     <= 0;
            add_sign_not_shifted_in <= 0;
            frac_shifted_in         <= 0;
            frac_not_shifted_in     <= 0;
            add_exp_max_in          <= 0;
            start_passthrough_2 <= 0;
        end
        else if(run) begin
            add_sign_shifted_in     <= add_sign_shifted_out;
            add_sign_not_shifted_in <= add_sign_not_shifted_out;
            frac_shifted_in         <= frac_shifted_out;
            frac_not_shifted_in     <= frac_not_shifted_out;
            add_exp_max_in          <= add_exp_max_out;
            start_passthrough_2 <= adder.start;
        end
        else begin
            add_sign_shifted_in     <= add_sign_shifted_in;
            add_sign_not_shifted_in <= add_sign_not_shifted_in;
            frac_shifted_in         <= frac_shifted_in;
            frac_not_shifted_in     <= frac_not_shifted_in;
            add_exp_max_in          <= add_exp_max_in;
            start_passthrough_2 <= start_passthrough_2;
        end
    end

    // signals connecting add stage2 with stage3
    logic add_sign_out, add_sign_in;
    logic [12:0] add_sum_out, add_sum_in;
    logic add_carry_out, add_carry_in;
    logic [4:0] add_exp_max_s2_out, add_exp_max_s3_in;

    ADD_step2 add2 (frac_shifted_in, add_sign_shifted_in, frac_not_shifted_in, add_sign_not_shifted_in, add_exp_max_in, add_sign_out, add_sum_out, add_carry_out, add_exp_max_s2_out);

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0) begin
            add_sign_in             <= 0;
            add_sum_in              <= 0;
            add_carry_in            <= 0;
            add_exp_max_s3_in       <= 0;
            start_passthrough_3 <= 0;
        end
        else if(run) begin
            add_sign_in             <= add_sign_out;
            add_sum_in              <= add_sum_out;
            add_carry_in            <= add_carry_out;
            add_exp_max_s3_in       <= add_exp_max_s2_out;
            start_passthrough_3 <= start_passthrough_2;
        end
        else begin
            add_sign_in             <= add_sign_in;
            add_sum_in              <= add_sum_in;
            add_carry_in            <= add_carry_in;
            add_exp_max_s3_in       <= add_exp_max_s3_in;
            start_passthrough_3 <= start_passthrough_3;
        end
    end

    // ADD stage3 outputs
    logic [15:0] accumulate_result;
    logic [4:0] add_flags;
    // Rounding mode: truncation. Maybe should pick something else?
    ADD_step3 add3(0, 0, 0, 0, 3'b001, add_exp_max_s3_in, add_sign_in, add_sum_in, add_carry_in, accumulate_result, add_flags);
    assign adder.add_output = add_flags[2] ? 16'b0111110000000000 : accumulate_result;   // Overflow handler



endmodule
