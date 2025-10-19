/*
  Chase Johnson
  cyjohnso@purdue.edu

  Connects Data Path Together
*/

// system interface
`include "system_if.vh"
//types
`include "isa_types.vh"
`include "ram_pkg.vh"
`include "ram_if.vh"

module system (input logic CLK, nrst, system_if.sys syif);

  import isa_pkg::*;

  // stopped running
  logic halt;

  // clock division
  parameter CLKDIV = 2;
  logic CPUCLK;
  logic [3:0] count;
  //logic CPUnrst;

  always_ff @(posedge CLK, negedge nrst)
  begin
    if (!nrst)
    begin
      count <= 0;
      CPUCLK <= 0;
    end
    else if (count == CLKDIV-2)
    begin
      count <= 0;
      CPUCLK <= ~CPUCLK;
    end
    else
    begin
      count <= count + 1;
    end
  end

  // interfaces
  ram_if                            prif ();

  // scheduler core processor
  scheduler_core                        CPU (CPUCLK, nrst, halt, prif);

  // memory
  ram                                   RAM (CLK, nrst, prif);

  // interface connections
  assign syif.halt = halt;
  assign syif.load = prif.ramload;

  // who has ram control
  assign prif.ramWEN = (syif.tbCTRL) ? syif.WEN : prif.memWEN;
  assign prif.ramREN = (syif.tbCTRL) ? syif.REN : prif.memREN;
  assign prif.ramaddr = (syif.tbCTRL) ? syif.addr : prif.memaddr;
  assign prif.ramstore = (syif.tbCTRL) ? syif.store : prif.memstore;

endmodule