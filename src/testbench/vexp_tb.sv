// vexp_tb.sv
`timescale 1ns/1ps

`include "vector_types.vh"
`include "vector_if.vh"
`include "vexp_if.vh"
`include "vaddsub_if.vh"

module vexp_tb;

  parameter PERIOD = 10;
  logic CLK = 0, nRST;

  always #(PERIOD/2) CLK++;

  vexp_if vexpif();

  vexp dut (
  .CLK   (CLK),
  .nRST  (nRST),
  .vexpif(vexpif)
  );

  localparam logic [15:0] FP16_P0   = 16'h0000; // +0
  localparam logic [15:0] FP16_N0   = 16'h8000; // -0
  localparam logic [15:0] FP16_ONE  = 16'h3C00; // +1
  localparam logic [15:0] FP16_NEG1 = 16'hBC00; // -1
  localparam logic [15:0] FP16_TWO  = 16'h4000; // +2
  localparam logic [15:0] FP16_HALF = 16'h3800; // +0.5
  localparam logic [15:0] FP16_PINF = 16'h7C00; // +Inf
  localparam logic [15:0] FP16_NINF = 16'hFC00; // -Inf
  localparam logic [15:0] FP16_QNAN = 16'h7E00; // qNaN

  int casenum;
  string casename;

initial begin

  casename = "NRST";
  casenum = 0;

  nRST = '0;

  vexpif.port_a = '0;
  vexpif.enable = '0;

  #(PERIOD * 10);

  //////////////////////////////////////////////////////

  nRST = 1'b1;
  
  //////////////////////////////////////////////////////

  casename = "e^0";
  casenum = 1;

  vexpif.port_a = '0;
  vexpif.enable = 1'b1;

  #(PERIOD * 60);

  //////////////////////////////////////////////////////

  casename = "e^1";
  casenum = 2;

  vexpif.port_a = FP16_ONE;
  vexpif.enable = 1'b1;

  #(PERIOD * 60);

  //////////////////////////////////////////////////////

  casename = "e^3";
  casenum = 3;

  vexpif.port_a = 16'b0_10000_1000000000;
  vexpif.enable = 1'b1;

  #(PERIOD * 60);

  //////////////////////////////////////////////////////

  casename = "e^1.5";
  casenum = 4;

  vexpif.port_a = 16'b0_01111_1000000000;
  vexpif.enable = 1'b1;

  #(PERIOD * 60);

  //////////////////////////////////////////////////////

  casename = "e^3.5";
  casenum = 5;

  vexpif.port_a = 16'b0_10000_1100000000;
  vexpif.enable = 1'b1;

  #(PERIOD * 60);

  //////////////////////////////////////////////////////

  casename = "Burst Request";
  casenum = 6;

  vexpif.port_a = FP16_ONE;
  vexpif.enable = 1'b1;

  #(PERIOD);

  vexpif.port_a = FP16_TWO;

  #(PERIOD);

  vexpif.port_a = FP16_NEG1;

  #(PERIOD);

  vexpif.port_a = FP16_HALF;

  #(PERIOD * 30);

  $stop;

end


endmodule
