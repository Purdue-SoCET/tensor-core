`timescale 1ns / 10ps
`include "isa_types.vh"
`include "datapath_types.vh"

`include "fetch_branch_if.vh"
`include "fetch_if.vh"
`include "fu_branch_predictor_if.vh"
`include "fu_branch_if.vh"

import isa_pkg::*;

module fetch_branch_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST;
  // clock
    always #(PERIOD/2) CLK++;

    fetch_branch_if fbif();
    
    fetch_branch DUT (.CLK(CLK), .nRST(nRST), .fbif(fbif));

    test PROG (CLK, nRST, fbif);
endmodule 

  program test (input logic CLK, 
                  output logic nRST, 
                  fetch_branch_if.tb fbif);

    parameter CLOCK_TIME = 10;
    string tb_testcase;
    initial begin
    //base case
    nRST = 0;

    // fbif.ihit = 0;
    tb_testcase = "Reset";
    fbif.imemload = '0;
    fbif.flush = '0;
    fbif.stall = '0;
    fbif.dispatch_free = '0;
    fbif.branch = '0;
    fbif.branch_type = 2'b00;
    fbif.branch_gate_sel = 1'b0;
    fbif.reg_a = 32'd0;
    fbif.reg_b = 32'd0;
    fbif.current_pc = 32'd0;
    fbif.imm = 32'd0;
    fbif.predicted_outcome = '0;

    @(posedge CLK);
    nRST = 1;
    #(CLOCK_TIME * 4);
    // fbif.ihit = 1;
    tb_testcase = "Stall";
    fbif.imemload = 32'hABCDEF01;
    fbif.flush = '0;
    fbif.stall = '1;
    fbif.dispatch_free = 1'b1;
    fbif.branch = '0;
    fbif.branch_type = 2'b00;
    fbif.branch_gate_sel = 1'b0;
    fbif.reg_a = 32'd0;
    fbif.reg_b = 32'd0;
    fbif.current_pc = 32'd4;
    fbif.imm = 32'd0;
    fbif.predicted_outcome = '0;

    #(CLOCK_TIME * 4);

    tb_testcase = "BEQ";
    fbif.imemload = 32'hABCDEF01;
    fbif.flush = '0;
    fbif.stall = '0;
    fbif.dispatch_free = 1'b1;
    fbif.branch = '1;
    fbif.branch_type = 2'b00;
    fbif.branch_gate_sel = 1'b0;
    fbif.reg_a = 32'd8;
    fbif.reg_b = 32'd8;
    fbif.current_pc = 32'd8;
    fbif.imm = 32'd64;
    fbif.predicted_outcome = '1;

    #(CLOCK_TIME * 4);

    tb_testcase = "Misprediction";
    fbif.imemload = 32'hABCDEF01;
    fbif.flush = '0;
    fbif.stall = '0;
    fbif.dispatch_free = 1'b1;
    fbif.branch = '1;
    fbif.branch_type = 2'b00;
    fbif.branch_gate_sel = 1'b0;
    fbif.reg_a = 32'd8;
    fbif.reg_b = 32'd8;
    fbif.current_pc = 32'd12;
    fbif.imm = 32'd42;
    fbif.predicted_outcome = '0;

    #(CLOCK_TIME * 4);
    
    $finish;
    end
  endprogram 
 
