`timescale 1ns/1ps

module gsau_control_unit_tb;
  import vector_pkg::*;
  import sys_arr_pkg::*;
  import types_pkg::*;

  // Parameters
  localparam VEGGIEREGS = 256;
  localparam FIFOSIZE   = 32*3*8;

  // Clock / reset
  logic CLK, nRST;
  always #5 CLK = ~CLK;  // 100 MHz

  // Interface
  gsau_control_unit_if gsau_if_inst();

  // DUT
  gsau_control_unit #(
    .VEGGIEREGS(VEGGIEREGS),
    .FIFOSIZE(FIFOSIZE)
  ) dut (
    .CLK(CLK),
    .nRST(nRST),
    .gsau_port(gsau_if_inst)
  );

  // Test sequence
  initial begin
    CLK  = 0;
    nRST = 0;
    gsau_if_inst.wb_output_ready = 1;
    gsau_if_inst.sa_fifo_has_space = 1;
    gsau_if_inst.sa_out_en = 0;
    gsau_if_inst.sb_nvalid = 0;
    gsau_if_inst.sb_nvdst = '0;
    gsau_if_inst.sa_array_output = '0;
    #20;
    nRST = 1;

    $display("[%0t] Reset done.", $time);

    // Simulate instruction dispatch to systolic array
    gsau_if_inst.sb_nvdst = 8'h0A;
    gsau_if_inst.sb_nvalid = 1;
    #10;
    gsau_if_inst.sb_nvalid = 0;

    // Systolic array produces output (WB ready)
    gsau_if_inst.sa_array_output = 512'hDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF;
    gsau_if_inst.sa_out_en = 1;
    gsau_if_inst.wb_output_ready = 1;  // WB ready
    #10;
    gsau_if_inst.sa_out_en = 0;

    // Expect writeback valid
    if (gsau_if_inst.wb_valid)
      $display("[%0t] ✅ Output accepted: wbdst=%0h", $time, gsau_if_inst.wb_wbdst);
    else
      $error("[%0t] ❌ WB not valid when expected", $time);

    // Stall condition (WB not ready)
    gsau_if_inst.sa_array_output = 512'hCAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE;
    gsau_if_inst.sa_out_en = 1;
    gsau_if_inst.wb_output_ready = 0;
    #10;

    if (gsau_if_inst.wb_valid)
      $error("[%0t] ❌ WB should have stalled but was valid", $time);
    else
      $display("[%0t] 🧱 Stall correctly applied.", $time);

    // Resume after stall
    gsau_if_inst.wb_output_ready = 1;
    #10;
    if (gsau_if_inst.wb_valid)
      $display("[%0t] ✅ Recovered from stall.", $time);
    else
      $error("[%0t] ❌ Did not resume after WB ready.", $time);

    #50;
    $display("✅ TEST COMPLETED.");
    $finish;
  end
endmodule