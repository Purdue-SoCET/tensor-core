`include "dram_pkg.vh"

`timescale 1 ns / 1 ns

module command_FSM_tb ();
    // import packages
    import dram_pkg::*;

    parameter PERIOD = 10;

    logic tb_CLK = 0, tb_nRST;

    // clock
    always #(PERIOD/2) tb_CLK++;

    //*****************************************************************************
    // Declare DUT Signals
    //*****************************************************************************
    command_fsm_if tb_cfsmif ();
    row_open_if tb_polif ();
    
    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    command_FSM DUT (.CLK(tb_CLK), .nRST(tb_nRST), .mycmd(tb_cfsmif), .polif(tb_polif));
endmodule