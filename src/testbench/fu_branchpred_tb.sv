`include "fu_branchpred_if.vh"
`include "cpu_types.vh"
`include "types_pkg.vh"

`timescale 1ns / 10ps

import cpu_types::*;
import types_pkg::*;

module fu_branchpred_tb;

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

fu_branchpred_if fubpif ();
fu_branchpred DUT (.CLK(tb_clk), .nRST(tb_nrst), .fubpif(fubpif));

string tb_test_case = "INIT";

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

    // Case 1
    tb_test_case = "Test 1: Backward Taken";
    fubpif.pc = 32'h00000010;
    #10;
    fubpif.update_pc = 32'h00000010;
    fubpif.update_btb = 1'b1;
    fubpif.branch_target = 32'h00000008;
    fubpif.branch_outcome = 1'b1;
    
    #10;
    fubpif.update_btb = 1'b1;
    #10;

    // Case 2
    tb_test_case = "Test 2: Forward Not Taken";
    fubpif.pc = 32'h00000020;
    #10;
    check_outputs(tb_test_case, fubpif.predicted_outcome, 1'b0, fubpif.predicted_target, 32'h00000024);

    $stop;
end

endmodule