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
  string test_name = "Reset";
  spif_tb.sStore_hit = 1'b0;
  spif_tb.instrFIFO_WEN = 1'b0;
  nRST = 1;
  #(PERIOD);

  nRST = 0;
  #(PERIOD * 2);

  nRST = 1;
  #(PERIOD);

  @(posedge CLK);

  test_name = "Load Instruction";
  @(negedge CLK);
  
  spif_tb.instrFIFO_WEN = 1'b1;
  spif_tb.instrFIFO_wdata = {2'b01, 4'h2, 32'hf0f0f0f0};
  @(negedge CLK);
  spif_tb.instrFIFO_WEN = 1'b0;
  #(PERIOD*5);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd0;
  spif_tb.load_data = 64'hfdecba0987654321;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*3);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd1;
  spif_tb.load_data = 64'h09374923094320fe;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*3);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd2;
  spif_tb.load_data = 64'hfffffffffffffff;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*3);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd3;
  spif_tb.load_data = 64'hf0f0f0f0f0f0f0f0;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*10);


  test_name = "Store Instruction";
  spif_tb.instrFIFO_WEN = 1'b1;
  spif_tb.instrFIFO_wdata = {2'b10, 4'h2, 32'hf0f0f0f0};
  @(negedge CLK);
  spif_tb.instrFIFO_WEN = 1'b0;
  #(PERIOD*5);
  spif_tb.sStore_hit = 1'b1;
  #(PERIOD);
  spif_tb.sStore_hit = 1'b0;
  #(PERIOD*5);
  spif_tb.sStore_hit = 1'b1;
  #(PERIOD);
  spif_tb.sStore_hit = 1'b0;
  #(PERIOD*5);
  spif_tb.sStore_hit = 1'b1;
  #(PERIOD);
  spif_tb.sStore_hit = 1'b0;
  #(PERIOD*5);
  spif_tb.sStore_hit = 1'b1;
  #(PERIOD);
  spif_tb.sStore_hit = 1'b0;

  test_name = "Load Instruction 2";
  
  spif_tb.sLoad_row = 2'd0;
  spif_tb.instrFIFO_WEN = 1'b1;
  spif_tb.instrFIFO_wdata = {2'b01, 4'hf, 32'hf0f0f0f0};
  @(negedge CLK);
  spif_tb.instrFIFO_WEN = 1'b0;
  #(PERIOD*5);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd0;
  spif_tb.load_data = 64'hfdecba0987654321;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*3);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd1;
  spif_tb.load_data = 64'h09374923094320fe;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*3);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd2;
  spif_tb.load_data = 64'hfffffffffffffff;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*3);
  spif_tb.sLoad_hit = 1'b1;
  spif_tb.sLoad_row = 2'd3;
  spif_tb.load_data = 64'hf0f0f0f0f0f0f0f0;
  @(negedge CLK);
  spif_tb.sLoad_hit = 1'b0;
  #(PERIOD*10);
  $finish;

end
endprogram