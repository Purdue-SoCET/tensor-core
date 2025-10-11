`include "fu_branch_predictor_if.vh"
`include "isa_types.vh"

`timescale 1ns / 10ps

import isa_pkg::*;

module fu_branch_predictor_tb;

// Parameters
localparam CLK_PERIOD = 1;

// Testbench Signals
logic tb_clk;
logic tb_nrst;

always
begin
    tb_clk = 1'b0;
    #(CLK_PERIOD/2.0);
    tb_clk = 1'b1;
    #(CLK_PERIOD/2.0);
end

fu_branch_predictor_if fubpif ();
fu_branch_predictor DUT (.CLK(tb_clk), .nRST(tb_nrst), .fubpif(fubpif));

string tb_test_case = "INIT";
integer tb_test_num = 0;

task check_outputs;
    input string test_name;
    input logic actual_outcome;
    input logic expected_outcome;
    input word_t actual_target;
    input word_t expected_target;
begin
    if (actual_outcome == expected_outcome && actual_target == expected_target) begin
        $display("PASSED %s", test_name);
    end else begin
        $display("FAILED %s", test_name);
    end
end
endtask

initial begin
    // Power on Reset
    tb_test_case = "Reset";
    tb_nrst = 1'b0;
    fubpif.pc = '0;
    fubpif.update_pc = '0;
    fubpif.update_btb = '0;
    fubpif.branch_outcome = '0;
    fubpif.branch_target = '0;

    #(CLK_PERIOD*2);
    tb_nrst = 1'b1;
    #(CLK_PERIOD*2);

    #20;

    // Misprediction (Initial)
    tb_test_case = "Test: Backward Taken";
    tb_test_num  = tb_test_num + 1;
    fubpif.pc = 32'h00000010;
    #10;
    check_outputs(tb_test_case, fubpif.predicted_outcome, 1'b0, fubpif.predicted_target, 32'h00000014);
    fubpif.update_btb = 1'b1;
    fubpif.update_pc = 32'h00000010;
    fubpif.branch_target = 32'h00000008; // Backward target
    fubpif.branch_outcome = 1'b1;
    
    #10;
    fubpif.update_btb = 1'b0;
    #10;

    // Correct Prediction (Learned after Case 1)
    tb_test_case = "Test: Backward Taken After Learning";
    tb_test_num  = tb_test_num + 1;
    fubpif.pc = 32'h00000010;
    #10;
    check_outputs(tb_test_case, fubpif.predicted_outcome, 1'b1, fubpif.predicted_target, 32'h00000008);

    // Correct Prediction
    tb_test_case = "Test: Forward Not Taken";
    tb_test_num  = tb_test_num + 1;
    fubpif.pc = 32'h00000020;
    #10;
    check_outputs(tb_test_case, fubpif.predicted_outcome, 1'b0, fubpif.predicted_target, 32'h00000024);

    // Misprediction
    tb_test_case = "Test: Forward Taken";
    tb_test_num  = tb_test_num + 1;
    fubpif.pc = 32'h00000030;
    #10;
    check_outputs(tb_test_case, fubpif.predicted_outcome, 1'b0, fubpif.predicted_target, 32'h00000034);
    fubpif.update_btb = 1'b1;
    fubpif.update_pc = 32'h00000030;
    fubpif.branch_outcome = 1'b1;        // Actual outcome
    fubpif.branch_target = 32'h00000040; // Forward target
    #10;
    fubpif.update_btb = 1'b0;
    #10;

    // Misprediction
    tb_test_case = "Test: Backward Not Taken";
    tb_test_num  = tb_test_num + 1;
    fubpif.pc = 32'h00000010; // PC used in Case 1
    #10;
    check_outputs(tb_test_case, fubpif.predicted_outcome, 1'b1, fubpif.predicted_target, 32'h00000008);
    fubpif.update_btb = 1'b1;
    fubpif.update_pc = 32'h00000010;
    fubpif.branch_outcome = 1'b0;
    fubpif.branch_target = 32'h00000008; // Backward target
    #10;
    fubpif.update_btb = 1'b0;
    #10;
    // Entry at index 4 should be invalidated at this point

    $stop;
end

endmodule