`timescale 1ns/1ps
`include "gsau_control_unit_if.vh"
`include "sync_fifo.sv"
`include "sys_arr_pkg.vh"
`include "vector_pkg.vh"

module gsau_control_unit_tb;

  //Parameters
  localparam VEGGIEREGS = 256;
  localparam FIFOSIZE   = 32*3*8;

  // Clock & Reset
  logic CLK;
  logic nRST;

  // GSAU interface
  gsau_control_unit_if.gsau gsau_port();

  // Instantiate GSAU Control Unit
  gsau_control_unit #(
    .VEGGIEREGS(VEGGIEREGS),
    .FIFOSIZE(FIFOSIZE)
  ) dut (
    .CLK(CLK),
    .nRST(nRST),
    .gsau_port(gsau_if_inst)
  );

  // --------------------------
  // Clock generation
  // --------------------------
  initial CLK = 0;
  always #5 CLK = ~CLK; // 100MHz clock

  // --------------------------
  // Reset
  // --------------------------
  task reset_dut();
    begin
      nRST = 0;
      repeat(5) @(posedge CLK);
      nRST = 1;
      @(posedge CLK);
    end
  endtask

  // --------------------------
  // Test Tasks
  // --------------------------
  // Task 0: Power on reset
  task test_power_on_reset();
    begin
      $display("Test 0: Power-on reset");
      reset_dut();
      assert(dut.state == dut.IDLE) else $fatal("FSM not in IDLE after reset");
    end
  endtask

  // Task 1: FSM correctness
  task test_fsm_correctness();
    begin
      $display("Test 1: FSM correctness");
      // Issue normal instruction
      gsau_port.sb_nvalid = 1;
      gsau_port.sb_nvdst  = 8'hAA;
      gsau_port.sb_weight = 0;
      gsau_port.veg_valid = 1;
      gsau_port.veg_vdata = 512'hDEADBEEFCAFEBABEDEADBEEFCAFEBABE;

      @(posedge CLK);
      gsau_port.sb_nvalid = 0;
      gsau_port.veg_valid = 0;

      // Wait for FSM to go through WAIT_OUTPUT -> SEND_OUTPUT
      repeat(3) @(posedge CLK);

      assert(dut.state == dut.SEND_OUTPUT || dut.state == dut.IDLE)
        else $fatal("FSM did not reach SEND_OUTPUT/IDLE properly");
    end
  endtask

  // Task 2: RD Queue full handling
  task test_rd_queue_full();
    begin
      $display("Test 2: RD Queue full handling");
      // Fill FIFO
      int i;
      for (i=0; i<dut.FIFO_DEPTH; i++) begin
        gsau_port.sb_nvalid = 1;
        gsau_port.sb_nvdst  = i;
        gsau_port.veg_valid = 1;
        gsau_port.veg_vdata = 512'h1;
        @(posedge CLK);
      end

      // FIFO should be full
      assert(dut.fifo_full) else $fatal("FIFO should be full");
      // Attempt new write
      gsau_port.sb_nvalid = 1;
      gsau_port.sb_nvdst  = 8'hFF;
      gsau_port.veg_valid = 1;
      @(posedge CLK);
      assert(!dut.o_sb_ready) else $fatal("Controller allowed new instruction when FIFO full");

      // Release
      gsau_port.sb_nvalid = 0;
      gsau_port.veg_valid = 0;
    end
  endtask

  // Task 3: RD Queue empty handling
  task test_rd_queue_empty();
    begin
      $display("Test 3: RD Queue empty handling");
      gsau_port.sa_out_en = 1; // attempt to read when FIFO empty
      @(posedge CLK);
      assert(dut.latched_vdst == 0) else $fatal("Empty FIFO produced data");
      gsau_port.sa_out_en = 0;
    end
  endtask

  // Task 4: WB ready
  task test_wb_ready();
    begin
      $display("Test 4: WB ready handling");
      // Issue instruction
      gsau_port.sb_nvalid = 1; gsau_port.sb_nvdst=8'h55;
      gsau_port.veg_valid = 1; gsau_port.veg_vdata=512'hABCD;
      @(posedge CLK);
      gsau_port.sb_nvalid = 0; gsau_port.veg_valid = 0;
      // SA produces output
      gsau_port.sa_out_en = 1;
      gsau_port.sa_array_output = 512'h1234;
      gsau_port.wb_output_ready = 1;
      @(posedge CLK);
      assert(dut.o_wb_valid == 0) else $fatal("WB valid not cleared after acceptance");
      gsau_port.sa_out_en = 0; gsau_port.wb_output_ready = 0;
    end
  endtask

  // Task 5: WB not ready
  task test_wb_not_ready();
    begin
      $display("Test 5: WB not ready stall");
      gsau_port.sb_nvalid = 1; gsau_port.sb_nvdst=8'h11;
      gsau_port.veg_valid = 1; gsau_port.veg_vdata=512'h2222;
      @(posedge CLK);
      gsau_port.sb_nvalid = 0; gsau_port.veg_valid = 0;
      gsau_port.sa_out_en = 1;
      gsau_port.sa_array_output = 512'h3333;
      gsau_port.wb_output_ready = 0;
      @(posedge CLK);
      assert(dut.o_wb_valid == 1) else $fatal("WB valid not high when WB not ready");
      gsau_port.sa_out_en = 0;
    end
  endtask

  // Task 6: Single normal instruction
  task test_single_instruction();
    begin
      $display("Test 6: Single normal instruction");
      gsau_port.sb_nvalid = 1; gsau_port.sb_nvdst=8'h42;
      gsau_port.veg_valid = 1; gsau_port.veg_vdata=512'hCAFEBABE;
      @(posedge CLK);
      gsau_port.sb_nvalid = 0; gsau_port.veg_valid = 0;
      @(posedge CLK); // allow FSM to process
      assert(dut.fifo_empty == 0) else $fatal("FIFO did not enqueue instruction");
    end
  endtask

  // Task 7: Back to back instructions
  task test_back_to_back();
    int i;
    begin
      $display("Test 7: Back-to-back instructions");
      for (i=0; i<5; i++) begin
        gsau_port.sb_nvalid = 1; gsau_port.sb_nvdst=i;
        gsau_port.veg_valid = 1; gsau_port.veg_vdata=512'h100+i;
        @(posedge CLK);
      end
      gsau_port.sb_nvalid = 0; gsau_port.veg_valid = 0;
    end
  endtask

  // Task 8: Randomized instruction stream
  task test_randomized();
    int i;
    logic [7:0] rand_vdst;
    begin
      $display("Test 8: Randomized instruction stream");
      for (i=0; i<20; i++) begin
        rand_vdst = $urandom_range(0,255);
        gsau_port.sb_nvalid = $urandom_range(0,1);
        gsau_port.sb_nvdst  = rand_vdst;
        gsau_port.sb_weight = $urandom_range(0,1);
        gsau_port.veg_valid = $urandom_range(0,1);
        gsau_port.veg_vdata = $urandom;
        gsau_port.wb_output_ready = $urandom_range(0,1);
        gsau_port.sa_out_en = $urandom_range(0,1);
        @(posedge CLK);
      end
      gsau_port.sb_nvalid = 0; gsau_port.veg_valid = 0;
      gsau_port.sa_out_en = 0; gsau_port.wb_output_ready = 0;
    end
  endtask

  // --------------------------
  // Run Test Plan
  // --------------------------
  initial begin
    $display("Starting GSAU Control Unit Testbench");

    test_power_on_reset();
    test_fsm_correctness();
    test_rd_queue_full();
    test_rd_queue_empty();
    test_wb_ready();
    test_wb_not_ready();
    test_single_instruction();
    test_back_to_back();
    test_randomized();

    $display("All tests completed successfully.");
    $finish;
  end

endmodule

// `timescale 1ns/1ps
// `include "sys_arr_pkg.vh"
// `include "vector_pkg.vh"

// module gsau_control_unit_tb;
//   import vector_pkg::*;
//   import sys_arr_pkg::*;

//   // Parameters
//   localparam VEGGIEREGS = 256;
//   localparam FIFOSIZE   = 32*3*8;

//   // Clock / reset
//   logic CLK, nRST;
//   always #5 CLK = ~CLK;  // 100 MHz

//   // Interface
//   gsau_control_unit_if gsau_if_inst();

//   // DUT
//   gsau_control_unit #(
//     .VEGGIEREGS(VEGGIEREGS),
//     .FIFOSIZE(FIFOSIZE)
//   ) dut (
//     .CLK(CLK),
//     .nRST(nRST),
//     .gsau_port(gsau_if_inst)
//   );

//   // Test sequence
//   initial begin
//     CLK  = 0;
//     nRST = 0;
//     gsau_if_inst.wb_output_ready = 1;
//     gsau_if_inst.sa_fifo_has_space = 1;
//     gsau_if_inst.sa_out_en = 0;
//     gsau_if_inst.sb_nvalid = 0;
//     gsau_if_inst.sb_nvdst = '0;
//     gsau_if_inst.sa_array_output = '0;
//     #20;
//     nRST = 1;

//     $display("[%0t] Reset done.", $time);

//     // Simulate instruction dispatch to systolic array
//     gsau_if_inst.sb_nvdst = 8'h0A;
//     gsau_if_inst.sb_nvalid = 1;
//     #10;
//     gsau_if_inst.sb_nvalid = 0;

//     // Systolic array produces output (WB ready)
//     gsau_if_inst.sa_array_output = 512'hDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF;
//     gsau_if_inst.sa_out_en = 1;
//     gsau_if_inst.wb_output_ready = 1;  // WB ready
//     #10;
//     gsau_if_inst.sa_out_en = 0;

//     // Expect writeback valid
//     if (gsau_if_inst.wb_valid)
//       $display("[%0t] ✅ Output accepted: wbdst=%0h", $time, gsau_if_inst.wb_wbdst);
//     else
//       $error("[%0t] ❌ WB not valid when expected", $time);

//     // Stall condition (WB not ready)
//     gsau_if_inst.sa_array_output = 512'hCAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE_CAFEBABE;
//     gsau_if_inst.sa_out_en = 1;
//     gsau_if_inst.wb_output_ready = 0;
//     #10;

//     if (gsau_if_inst.wb_valid)
//       $error("[%0t] ❌ WB should have stalled but was valid", $time);
//     else
//       $display("[%0t] 🧱 Stall correctly applied.", $time);

//     // Resume after stall
//     gsau_if_inst.wb_output_ready = 1;
//     #10;
//     if (gsau_if_inst.wb_valid)
//       $display("[%0t] ✅ Recovered from stall.", $time);
//     else
//       $error("[%0t] ❌ Did not resume after WB ready.", $time);

//     #50;
//     $display("✅ TEST COMPLETED.");
//     $finish;
//   end
// endmodule