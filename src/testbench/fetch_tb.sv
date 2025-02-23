`include "fetch_if.vh"
`include "isa_types.vh"

`timescale 1 ns / 1 ns

import isa_pkg::*;

module fetch_tb;
  string tb_test_case = "INIT";
  integer tb_test_num = 0;

  logic CLK = 0;
  parameter PERIOD = 10;

  logic nRST;
  logic tb_ihit;

  always #(PERIOD/2) CLK++;

  fetch_if fif ();
  fetch DUT(.CLK(CLK), .nRST(nRST), .ihit(tb_ihit), .fif(fif));

  task check_output;
    input word_t actual_output;
    input word_t expected_output;
    input string test_name;
    begin
        assert (actual_output == expected_output) else $error("%s failed", test_name);
    end
  endtask

  initial begin
    // Reset
    nRST = 1'b1;
    tb_ihit = 1'b1;
    fif.flush = 1'b0;
    fif.stall = 1'b0;
    fif.dispatch_free = 1'b1;
    fif.misprediction = 1'b0;
    fif.correct_target = 32'd0;
    fif.pc_prediction = 32'd0;
    nRST = 1'b0;
    #10;
    nRST = 1'b1;
    fif.correct_target = 32'h00001000;
    fif.pc_prediction = 32'hDEADBEEF;
    #10;

    tb_test_case = "Misprediction Test";
    tb_test_num = tb_test_num + 1;
    fif.imemload = 32'hACE1ACE1;
    fif.misprediction = 1'b1;
    fif.correct_pc = 32'hABCDEF01;
    #(PERIOD * 6);
    check_output(fif.instr, 32'hACE1ACE1, tb_test_case);
    check_output(fif.pc, 32'h00001000, tb_test_case);

    tb_test_case = "Correct Prediction Test";
    tb_test_num = tb_test_num + 1;
    fif.misprediction = 1'b0;
    fif.imemload = 32'hACE2ACE2;
    #(PERIOD * 6);
    check_output(fif.instr, 32'hACE2ACE2, tb_test_case);
    check_output(fif.pc, 32'hDEADBEEF, tb_test_case);

    tb_test_case = "Stall Test";
    tb_test_num = tb_test_num + 1;
    fif.misprediction = 1'b0;
    fif.correct_pc = 32'd0;
    fif.imemload = 32'hACE2ACE2;
    fif.stall = 1'b1;
    fif.correct_target = 32'h00004000;
    fif.pc_prediction = 32'hAABBCCDD;
    #(PERIOD * 6);
    check_output(fif.instr, 32'hACE2ACE2, tb_test_case);
    check_output(fif.pc, 32'hDEADBEEF, tb_test_case);

    tb_test_case = "Dispatch Busy Test";
    tb_test_num = tb_test_num + 1;
    fif.misprediction = 1'b0;
    fif.imemload = 32'hACE2ACE2;
    fif.stall = 1'b0;
    fif.correct_pc = 32'd0;
    fif.dispatch_free = 1'b0;
    fif.correct_target = 32'h00004000;
    fif.pc_prediction = 32'hAABBCCDD;
    #(PERIOD * 6);
    check_output(fif.instr, 32'hACE2ACE2, tb_test_case);
    check_output(fif.pc, 32'hDEADBEEF, tb_test_case);

    $stop;
  end
endmodule