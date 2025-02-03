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
logic tb_enable;
logic tb_ihit;
logic [0:15] tb_count;

always
begin
    tb_clk = 1'b0;
    #(CLK_PERIOD/2.0);
    tb_clk = 1'b1;
    #(CLK_PERIOD/2.0);
end

fu_branchpred_if fubpif ();
fu_branchpred DUT (.CLK(tb_clk), .nRST(tb_nrst), .ihit(tb_ihit), .fubpif(fubpif));

string tb_test_case = "INIT";

initial begin
    // Power on Reset
    tb_test_case = "Reset";
    tb_nrst = 1'b0;
    tb_ihit = 1'b0;
    fubpif.branch_outcome = '0;
    fubpif.update_btb = '0;
    fubpif.branch_target = '0;
    fubpif.pc_fetch = '0;
    fubpif.pc = '0;

    #(CLK_PERIOD*2);
    tb_nrst = 1'b1;
    #(CLK_PERIOD*2);

    #(CLK_PERIOD*32);

    tb_test_case = "Test 1: Index 64";
    fubpif.update_btb = '1;
    tb_ihit = 1'b1;
    fubpif.pc = 32'h00000100;
    fubpif.pc_fetch = 32'h00000080;
    fubpif.branch_target = 32'h00000060;

    #(CLK_PERIOD*32);
    fubpif.pc = 32'h00000120;
    fubpif.pc_fetch = 32'h00000100;

    #(CLK_PERIOD*32);

    tb_test_case = "Test 2";
    tb_ihit = 1'b0;
    fubpif.update_btb = '0;
    fubpif.pc = 32'h00000124;
    fubpif.pc_fetch = 32'h00000104;

    #(CLK_PERIOD*32);

    fubpif.pc = 32'h00000128;
    fubpif.pc_fetch = 32'h00000104;

    #(CLK_PERIOD*32);

    tb_ihit = 1'b1;
    fubpif.update_btb = '1;

    #(CLK_PERIOD*32);
    tb_ihit = 1'b0;
    fubpif.update_btb = '0;

    #(CLK_PERIOD*32);

    $stop;
end

endmodule