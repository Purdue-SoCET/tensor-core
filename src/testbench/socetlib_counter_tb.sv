`include "socetlib_counter_if.vh"

`timescale 1 ns / 1 ns

module socetlib_counter_tb ();

    parameter PERIOD = 10;

    logic tb_CLK = 0, tb_nRST;

    // clock
    always #(PERIOD/2) tb_CLK++;

    parameter NBITS = 32;

    //*****************************************************************************
    // Declare DUT Signals
    //*****************************************************************************
    logic clear;
    logic count_enable;
    logic [(NBITS - 1) : 0] overflow_val;
    logic [(NBITS - 1) : 0] count_out;
    logic overflow_flag;
    
    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    socetlib_counter DUT (.CLK(tb_CLK), .nRST(tb_nRST), .clear(clear),
                          .count_enable(count_enable), .overflow_val(overflow_val),
                          .count_out(count_out), .overflow_flag(overflow_flag));
endmodule