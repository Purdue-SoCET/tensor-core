`include "dram_pkg.vh"

`timescale 1 ns / 1 ns

module row_open_tb ();
    // import packages
    import dram_pkg::*;

    parameter PERIOD = 10;

    logic tb_CLK = 0, tb_nRST;

    // clock
    always #(PERIOD/2) tb_CLK++;

    //*****************************************************************************
    // Declare DUT Signals
    //*****************************************************************************
    row_open_if tb_polif ();
    address_mapper_if tb_amif ();
    
    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    row_open DUT (.CLK(tb_CLK), .nRST(tb_nRST), .pol_if(tb_polif), .amif(tb_amif));
endmodule