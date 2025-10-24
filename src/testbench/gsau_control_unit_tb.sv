// `timescale 1ns/1ps
// `include "gsau_control_unit_if.vh"
// `include "sys_arr_pkg.vh"
// `include "vector_pkg.vh"

// module gsau_control_unit_tb;
//   import sys_arr_pkg::*;
//   import vector_pkg::*;

//   // -----------------------
//   // Parameters
//   // -----------------------
//   localparam VEGGIEREGS = 256;
//   localparam FIFOSIZE   = 32*3*8;

//   // -----------------------
//   // Clock and Reset
//   // -----------------------
//   logic CLK;
//   logic nRST;
//   initial CLK = 0;
//   always #5 CLK = ~CLK; // 100 MHz

//   task reset_dut();
//     nRST = 0;
//     repeat(5) @(posedge CLK);
//     nRST = 1;
//     repeat(2) @(posedge CLK);
//   endtask

//   // -----------------------
//   // Interfaces
//   // -----------------------
//   gsau_control_unit_if gsau_port();

//   // -----------------------
//   // DUT Instantiation
//   // -----------------------
//   gsau_control_unit #(
//     .VEGGIEREGS(VEGGIEREGS),
//     .FIFOSIZE(FIFOSIZE)
//   ) dut (
//     .CLK(CLK),
//     .nRST(nRST),
//     .gsau_port(gsau_port)
//   );

//   // -----------------------
//   // Blackbox Systolic Array
//   // -----------------------
//   // Simplified version for validation only
//   logic sa_ready;
//   logic [511:0] sa_output;

//   always_ff @(posedge CLK or negedge nRST) begin
//     if (!nRST) begin
//       sa_output <= '0;
//       sa_ready  <= 1'b1;
//     end else if (gsau_port.sa_out_en) begin
//       sa_output <= (gsau_port.veg_vdata * 32'h4D); // Fake dot product, with decimal 77
//       sa_ready  <= 1'b1;
//     end
//   end

//   assign gsau_port.sa_array_output = sa_output;
//   assign gsau_port.sa_fifo_has_space = sa_ready;

//   // -----------------------
//   // FIFO vdst
//   // -----------------------
//   logic [31:0] fifo_mem [0:63];
//   int wr_ptr, rd_ptr, fifo_count;

//   task fifo_push(input [31:0] val);
//     if (fifo_count < 64) begin
//       fifo_mem[wr_ptr] = val;
//       wr_ptr = (wr_ptr + 1) % 64;
//       fifo_count++;
//     end else begin
//       $fatal("FIFO overflow at time %t", $time);
//     end
//   endtask

//   task fifo_pop(output [31:0] val);
//     if (fifo_count > 0) begin
//       val = fifo_mem[rd_ptr];
//       rd_ptr = (rd_ptr + 1) % 64;
//       fifo_count--;
//     end else begin
//       val = '0;
//       $display("Warning: FIFO underflow");
//     end
//   endtask

//   // -----------------------
//   // Test 0: Power-on Reset
//   // -----------------------
//   task test0_power_on_reset();
//     $display("\n[0] Power-on Reset");
//     reset_dut();
//   endtask

//   // -----------------------
//   // Test 2: RD Queue Full Handling
//   // -----------------------
//   task test2_rd_queue_full();
//     $display("\n[2] RD Queue Full Handling");
//     reset_dut();
//     repeat (dut.FIFO_DEPTH) begin
//       gsau_port.sb_nvalid = 1;
//       gsau_port.sb_nvdst = $urandom_range(0,255);
//       gsau_port.veg_valid = 1;
//       @(posedge CLK);
//     end
//     gsau_port.sb_nvalid = 1;
//     gsau_port.veg_valid = 1;
//     @(posedge CLK);
//     assert(!gsau_port.sb_ready)
//       else $fatal("Controller accepted data when FIFO full");
//   endtask

//   // -----------------------
//   // Test 3: RD Queue Empty Handling
//   // -----------------------
//   task test3_rd_queue_empty();
//     $display("\n[3] RD Queue Empty Handling");
//     reset_dut();
//     gsau_port.sa_out_en = 1;
//     @(posedge CLK);
//     assert(dut.fifo_empty)
//       else $fatal("Expected FIFO empty");
//   endtask

//   // -----------------------
//   // Test 4: WB Ready
//   // -----------------------
//   task test4_wb_ready();
//     $display("\n[4] WB Ready");
//     reset_dut();
//     gsau_port.sb_nvalid = 1;
//     gsau_port.veg_valid = 1;
//     @(posedge CLK);
//     gsau_port.sb_nvalid = 0;
//     gsau_port.veg_valid = 0;

//     gsau_port.sa_out_en = 1;
//     gsau_port.sa_array_output = 512'hAABBCCDD;
//     gsau_port.wb_output_ready = 1;
//     @(posedge CLK);

//     assert(gsau_port.wb_valid == 0)
//       else $fatal("Writeback not cleared properly");
//   endtask

//   // -----------------------
//   // Test 5: WB Not Ready (Stall)
//   // -----------------------
//   task test5_wb_not_ready();
//     $display("\n[5] WB Not Ready (Stall)");
//     reset_dut();
//     gsau_port.sb_nvalid = 1;
//     gsau_port.veg_valid = 1;
//     @(posedge CLK);
//     gsau_port.sb_nvalid = 0;
//     gsau_port.veg_valid = 0;
//     gsau_port.sa_out_en = 1;
//     gsau_port.wb_output_ready = 0;
//     @(posedge CLK);
//     assert(gsau_port.wb_valid == 1)
//       else $fatal("Controller didn’t stall when WB not ready");
//   endtask

//   // -----------------------
//   // Test 6: Send Normal Weights
//   // -----------------------
//   task test6_send_normal_weights();
//     $display("\n[6] Send Normal Weights");
//     reset_dut();
//     gsau_port.sb_weight = 1;
//     gsau_port.sb_nvalid = 1;
//     gsau_port.sb_nvdst = 8'h10;
//     @(posedge CLK);
//     gsau_port.sb_nvalid = 0;
//     gsau_port.sb_weight = 0;
//   endtask

//   // -----------------------
//   // Test 7: Single Normal Instruction
//   // -----------------------
//   task test7_single_normal_instruction();
//     $display("\n[7] Single Normal Instruction");
//     reset_dut();
//     gsau_port.sb_nvalid = 1;
//     gsau_port.sb_nvdst  = 8'h42;
//     gsau_port.veg_valid = 1;
//     gsau_port.veg_vdata = 512'hCAFEBABE;
//     @(posedge CLK);
//     gsau_port.sb_nvalid = 0;
//     gsau_port.veg_valid = 0;
//     @(posedge CLK);
//     assert(!dut.fifo_empty)
//       else $fatal("Instruction not enqueued");
//   endtask

//   // -----------------------
//   // Test 8: Back-to-Back Instructions
//   // -----------------------
//   task test8_back_to_back();
//     $display("\n[8] Back-to-Back Instructions");
//     reset_dut();
//     repeat (5) begin
//       gsau_port.sb_nvalid = 1;
//       gsau_port.veg_valid = 1;
//       gsau_port.sb_nvdst = $urandom_range(0,255);
//       @(posedge CLK);
//     end
//     gsau_port.sb_nvalid = 0;
//     gsau_port.veg_valid = 0;
//     assert(dut.fifo_count >= 5)
//       else $fatal("Back-to-back issue failed");
//   endtask

//   // -----------------------
//   // Test 9: Randomized Instruction Stream
//   // -----------------------
//   task test9_randomized_stream();
//     $display("\n[9] Randomized Instruction Stream");
//     reset_dut();
//     repeat (30) begin
//       gsau_port.sb_nvalid = $urandom_range(0,1);
//       gsau_port.veg_valid = $urandom_range(0,1);
//       gsau_port.sa_out_en = $urandom_range(0,1);
//       gsau_port.wb_output_ready = $urandom_range(0,1);
//       @(posedge CLK);
//     end
//   endtask

//   // -----------------------
//   // Test 10: Send Weight During Compute
//   // -----------------------
//   task test10_send_weight_during_compute();
//     $display("\n[10] Send Weight During Compute");
//     reset_dut();
//     gsau_port.sb_weight = 1;
//     gsau_port.sb_nvalid = 1;
//     @(posedge CLK);
//     gsau_port.sb_weight = 0;
//     gsau_port.sb_nvalid = 0;

//     gsau_port.sa_out_en = 1; // simulate running compute
//     gsau_port.sb_weight = 1; // try sending new weight mid-compute
//     @(posedge CLK);
//     // assert(dut.state != dut.LOAD_WEIGHT)
//     //   else $fatal("Sent weight while compute in progress");
//   endtask

//   // -----------------------
//   // Test Sequence
//   // -----------------------
//   initial begin
//     $display("======== GSAU CONTROL UNIT TESTBENCH START ========");
//     test0_power_on_reset();
//     test2_rd_queue_full();
//     test3_rd_queue_empty();
//     test4_wb_ready();
//     test5_wb_not_ready();
//     test6_send_normal_weights();
//     test7_single_normal_instruction();
//     test8_back_to_back();
//     test9_randomized_stream();
//     test10_send_weight_during_compute();
//     $display("======== ALL TESTS PASSED ========");
//     $finish;
//   end

// endmodule

`timescale 1ns/1ps
`include "gsau_control_unit_if.vh"
`include "sys_arr_pkg.vh"
`include "vector_pkg.vh"

module gsau_control_unit_tb;

  import vector_pkg::*;
  import sys_arr_pkg::*;

  // Parameters
  localparam VEGGIEREGS = 256;
  localparam FIFOSIZE   = 32*3*8;

  // Clock & Reset
  logic CLK;
  logic nRST;

  // Interface instance
  gsau_control_unit_if gsau_port();

  // DUT instance
  gsau_control_unit #(
    .VEGGIEREGS(VEGGIEREGS),
    .FIFOSIZE(FIFOSIZE)
  ) dut (
    .CLK(CLK),
    .nRST(nRST),
    .gsau_port(gsau_port)
  );

  // Clock generation
  initial CLK = 0;
  always #5 CLK = ~CLK; // 100 MHz clock

  // Reset sequence
  task reset_dut();
    nRST = 0;
    repeat (5) @(posedge CLK);
    nRST = 1;
    @(posedge CLK);
  endtask

  ///////////////////////////////////////////////////////////////
  // STUB MODULE BEHAVIOR (Veggie File, Scoreboard, WB Buffer, SA)
  ///////////////////////////////////////////////////////////////

  // Fake systolic array behavior
  // Produces output 3 cycles after sa_input_en
  initial begin
    gsau_port.sa_fifo_has_space = 1;
    gsau_port.sa_out_valid = 0;
    gsau_port.sa_array_output = '0;
    wait (nRST);

    forever begin
      @(posedge CLK);
      if (gsau_port.sa_input_en) begin
        fork
          begin
            repeat (3) @(posedge CLK);
            gsau_port.sa_array_output = 512'hDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF;
            gsau_port.sa_out_valid = 1;
            @(posedge CLK);
            gsau_port.sa_out_valid = 0;
          end
        join_none
      end
    end
  end

  // WB Buffer (accepts everything unless test says otherwise)
  initial begin
    gsau_port.wb_output_ready = 1;
  end

  // Default Veggie File
  initial begin
    gsau_port.veg_vdata1 = 512'h1111_1111_1111_1111;
    gsau_port.veg_vdata2 = 512'h2222_2222_2222_2222;
    gsau_port.veg_valid  = 1;
  end

  ///////////////////////////////////////////////////////////////
  // TASKS FOR CONTROL SIGNAL STIMULI
  ///////////////////////////////////////////////////////////////

  task send_scoreboard_entry(
    input [7:0] dst,
    input bit weight
  );
    gsau_port.sb_vdst   = dst;
    gsau_port.sb_weight = weight;
    gsau_port.sb_valid  = 1'b1;
    @(posedge CLK);
    gsau_port.sb_valid  = 1'b0;
  endtask

  task toggle_wb_ready(input bit ready);
    gsau_port.wb_output_ready = ready;
    @(posedge CLK);
  endtask

  ///////////////////////////////////////////////////////////////
  // TESTCASES
  ///////////////////////////////////////////////////////////////
  string test;

  initial begin
    $display("==== Starting GSAU Control Unit Testbench ====");
    reset_dut();

    // Test 0: Power-on reset
    $display("[T0] Reset Test");
    test = "Power On Reset";
    assert(!gsau_port.wb_valid) else $error("WB valid not cleared!");
    assert(!gsau_port.sa_input_en) else $error("SA input enable not cleared!");

    // Test 1: Normal instruction issue
    $display("[T1] Issue normal instruction");
    test = "normal instruction";
    send_scoreboard_entry(8'd5, 1'b0);
    repeat (5) @(posedge CLK);

    // Test 2: Weight load
    $display("[T2] Send weight");
    test = "send weights";
    send_scoreboard_entry(8'd0, 1'b1);
    repeat (5) @(posedge CLK);

    // Test 3: Backpressure from WB (stall)
    $display("[T3] WB Not Ready Stall");
    test = "stall for wb not ready";
    toggle_wb_ready(0);
    send_scoreboard_entry(8'd10, 1'b0);
    repeat (5) @(posedge CLK);
    toggle_wb_ready(1);
    repeat (10) @(posedge CLK);

    // Test 4: FIFO Full Behavior
    $display("[T4] FIFO Full Handling");
    test = "fifo full handling";
    repeat (64) send_scoreboard_entry($urandom_range(0, 255), 0);
    repeat (10) @(posedge CLK);

    // Test 5: Randomized traffic
    $display("[T5] Randomized Stress");
    test = "randomized stream";
    repeat (30) begin
      send_scoreboard_entry($urandom_range(0,255), $urandom_range(0,1));
      repeat ($urandom_range(2,5)) @(posedge CLK);
    end

    $display("==== All Tests Complete ====");
    $finish;
  end

endmodule