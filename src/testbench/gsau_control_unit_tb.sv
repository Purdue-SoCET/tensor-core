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
  logic ready;

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

  simple_systolic_model systolic_array (
    .CLK(CLK),
    .nRST(nRST),
    .output_ready(gsau_port.sa_input_en),
    .output_valid(gsau_port.sa_out_valid),
    .output_data(gsau_port.sa_array_output)
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
    @(posedge CLK);
  endtask

  ///////////////////////////////////////////////////////////////
  // STUB MODULE BEHAVIOR (Veggie File, Scoreboard, WB Buffer, SA)
  ///////////////////////////////////////////////////////////////

  // Fake systolic array behavior
  // Produces output 3 cycles after sa_input_en
  initial begin
    gsau_port.sa_fifo_has_space = 1;
    //gsau_port.sa_out_valid = 0;
    //gsau_port.sa_array_output = '0;
    gsau_port.wb_output_ready = 1;
    gsau_port.veg_vdata1 = 512'h1111_1111_1111_1111; // default values for veggie inputs/weights
    gsau_port.veg_vdata2 = 512'h2222_2222_2222_2222; // default values for veggie psums
    gsau_port.veg_valid  = 1;
    wait (nRST); // wait for nRST to go high
    /*
    forever begin
      @(posedge CLK);
      if (gsau_port.sa_input_en) begin
        fork
          begin
            repeat (3) @(posedge CLK);
            //gsau_port.sa_array_output = 512'hADDED;
            //gsau_port.sa_out_valid = 1;
            @(posedge CLK);
            //gsau_port.sa_out_valid = 0;
            //gsau_port.sa_array_output = 512'h0;
          end
        join_none
      end
    end*/
  end

  ///////////////////////////////////////////////////////////////
  // TASKS FOR CONTROL SIGNAL STIMULI
  ///////////////////////////////////////////////////////////////

  task send_scoreboard_entry (
    input [7:0] dst,
    input bit weight,
    input [511:0] vdata1, vdata2
  );
    wait(gsau_port.sb_ready);
    gsau_port.veg_vdata1 = vdata1;
    gsau_port.veg_vdata2 = vdata2;
    gsau_port.sb_vdst   = dst;
    gsau_port.sb_weight = weight;
    gsau_port.sb_valid  = 1'b1;
    @(posedge CLK);
    gsau_port.sb_valid  = 1'b0;
    gsau_port.sb_vdst   = '0;
    gsau_port.sb_weight = 1'b0;
    gsau_port.veg_vdata1 = 0;
    gsau_port.veg_vdata2 = 0;
  endtask

  task toggle_wb_ready(input bit ready);
    gsau_port.wb_output_ready = ready;
    @(posedge CLK);
  endtask

  ///////////////////////////////////////////////////////////////
  // TESTCASES
  ///////////////////////////////////////////////////////////////
  string test;
  logic [511:0] random_data1, random_data2;

  initial begin
    reset_dut();

    // Test 0: Power-on reset
    $display("[T0] Reset Test");
    test = "0 Power On Reset";
    assert(!gsau_port.wb_valid) else $error("TEST 0 WB valid not cleared!");
    assert(!gsau_port.sa_input_en) else $error("TEST 0 SA input enable not cleared!");

    // Test 1: Normal instruction issue
    $display("[T1] Issue normal instruction");
    test = "1 normal instruction";
    send_scoreboard_entry(8'd5, 1'b0, 512'h1111_1111_1111_1111, 512'h2222_2222_2222_2222);
    wait(gsau_port.wb_valid == 1);
    assert(gsau_port.wb_wbdst == 8'd5) else $error("TEST 1 WB destination mismatch!");
    repeat (5) @(posedge CLK);

    // Test 2: Weight load
    $display("[T2] Send weight");
    test = "2 send weights";
    send_scoreboard_entry(8'd0, 1'b1, 512'hCAFE, 512'h0);
    repeat (5) @(posedge CLK);

    // Test 3: Backpressure from WB (stall)
    $display("[T3] WB Not Ready Stall");
    test = "3 stall for wb not ready";
    toggle_wb_ready(0);
    fork
      begin
        // will wait for sb_ready
        send_scoreboard_entry(8'd10, 1'b0, 512'h3333_3333_3333_3333, 512'h4444_4444_4444_4444);
      end
      begin
        repeat ($urandom_range(5, 15)) @(posedge CLK);
        gsau_port.wb_output_ready = 1;
      end
    join
    repeat (10) @(posedge CLK);

    // Test 4: FIFO Full Behavior
    $display("[T4] FIFO Full Handling");
    test = "4 fifo full handling";
    repeat (96) begin
      void'(std::randomize(random_data1));
      void'(std::randomize(random_data2));
      send_scoreboard_entry($urandom_range(0, 255), 0, random_data1, random_data2);
    end 
    repeat (10) @(posedge CLK);

    // Test 5: Randomized traffic
    $display("[T5] Randomized Stress");
    test = "5 randomized stream";
    repeat (30) begin
      void'(std::randomize(random_data1));
      void'(std::randomize(random_data2));
      send_scoreboard_entry($urandom_range(0,255), $urandom_range(0,1), random_data1, random_data2);
      repeat ($urandom_range(2,5)) @(posedge CLK);
    end

    $display("==== All Tests Complete ====");
    $finish;
  end

endmodule