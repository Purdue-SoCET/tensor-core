`timescale 1ns/1ps
`include "scratchpad_if.vh"
`include "scratchpad_types_pkg.vh"

module r_fsm_tb;

  logic clk;
  logic n_rst;

  scpad_if sif();

  // DUT
  r_fsm #(.VC_ID(0)) dut (
    .clk   (clk),
    .n_rst (n_rst),
    .sif   (sif)
  );

  initial clk = 0;
  always #5 clk = ~clk; // 100MHz

  // Reset task
  task reset_dut();
    begin
      n_rst = 0;
      sif.start       = 0;
      sif.desc_valid  = 0;
      sif.rdata_valid = 0;
      #20;
      n_rst = 1;
    end
  endtask

  initial begin
    $display("[%0t] Starting r_fsm_tb...", $time);
    reset_dut();

    // Test 1: single descriptor
    @(posedge clk);
    sif.start      <= 1;
    sif.desc_valid <= 1;
    @(posedge clk);
    sif.start      <= 0;
    sif.desc_valid <= 0;

    wait(sif.req_valid);
    $display("[%0t] Req issued: addr=%h", $time, sif.addr);

    repeat (3) @(posedge clk);
    sif.rdata_valid <= 1;
    @(posedge clk);
    sif.rdata_valid <= 0;

    wait(sif.done);
    $display("[%0t] Done received", $time);

    // Test 2: multiple back-to-back reads
    repeat (3) begin
      @(posedge clk);
      sif.start      <= 1;
      sif.desc_valid <= 1;
      @(posedge clk);
      sif.start      <= 0;
      sif.desc_valid <= 0;

      wait(sif.req_valid);
      repeat (2) @(posedge clk);
      sif.rdata_valid <= 1;
      @(posedge clk);
      sif.rdata_valid <= 0;

      wait(sif.done);
      $display("[%0t] Done for one descriptor", $time);
    end

    $display("[%0t] Test completed!", $time);
    $finish;
  end

  // Simple monitor
  always @(posedge clk) begin
    if (sif.req_valid)
      $display("[%0t] FSM requesting addr=%h", $time, sif.addr);
    if (sif.done)
      $display("[%0t] FSM finished transaction", $time);
  end

endmodule
