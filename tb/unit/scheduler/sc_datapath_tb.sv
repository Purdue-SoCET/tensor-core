/*
  Chase Johnson
  cyjohnso@purdue.edu

  System Test Bench for Scheduler Core
*/

// interface
`include "system_if.vh"

// types
`include "datapath_types.vh"

// mapped timing needs this. 1ns is too fast
`timescale 1 ns / 1 ns

module sc_datapath_tb;
  // clock period
  parameter PERIOD = 10;

  // signals
  logic CLK = 1, nRST;

  // clock
  always #(PERIOD/2) CLK++;

  // interface
  datapath_cache_if                           dcif();

  // test program
  test                                PROG (CLK,nRST,dcif);

  // dut
  sc_datapath                              DUT (CLK,nRST,dcif);
endmodule

program test(input logic CLK, output logic nRST, datapath_cache_if.cache dcif);
  
  parameter PERIOD = 10;
  
  // import word type
  import isa_pkg::word_t;

  // number of cycles
  int unsigned cycles = 0;

  initial
  begin
    nRST = 0;
    @(posedge CLK);
    $display("Starting Scheduler Core:");
    nRST = 1;
    

    #(12*PERIOD)

    $finish;
  end

endprogram