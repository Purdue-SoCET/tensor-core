`include "dram_pkg.vh"

`timescale 1 ns / 1 ns

module init_state_tb ();
    // import packages
    import dram_pkg::*;

    parameter PERIOD = 10;

    logic tb_CLK = 0, tb_nRST;

    // clock
    always #(PERIOD/2) tb_CLK++;

    //*****************************************************************************
    // Declare DUT Signals
    //*****************************************************************************
    init_state_if tb_initif ();
    
    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    init_state DUT (.CLK(tb_CLK), .nRST(tb_nRST), .it(tb_initif));
endmodule