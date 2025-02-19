`include "scratchpad_if.vh"

`timescale 1 ns / 1 ns

module scratchpad_tb();
  parameter PERIOD = 10;

  logic CLK = 0, nRST;

  // clock
  always #(PERIOD/2) CLK++;

  // interfaces
  scratchpad_if spif ();

  // test program
  test PROG (CLK, nRST, spif);

  // DUT
  scratchpad DUT(CLK, nRST, spif);


endmodule

program test(
  input logic CLK, 
  output logic nRST,
  scratchpad_if.tb spif_tb
);
parameter PERIOD = 10;

initial begin

  nRST = 1;
  #(PERIOD);

  nRST = 0;
  #(PERIOD * 2);

  nRST = 1;
  #(PERIOD);

  @(posedge CLK);

end
endprogram