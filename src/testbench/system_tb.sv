/*
  Chase Johnson
  cyjohnso@purdue.edu

  System Test Bench for Scheduler Core
*/

// interface
`include "system_if.vh"

// types
`include "datapath_types.vh"
`include "isa_types.vh"
`include "datapath_types.vh"
`include "ram_pkg.vh"
// `include "types_pkg.vh"
`include "cpu_ram_if.vh"
`include "datapath_cache_if.vh"
`include "caches_if.vh"
`include "arbiter_caches_if.vh"
`include "scratchpad_if.vh"
`include "systolic_array_if.vh"
`include "main_mem_if.vh"

// mapped timing needs this. 1ns is too fast
`timescale 1 ns / 1 ns

module system_tb;
  // clock period
  parameter PERIOD = 20;

  // signals
  logic CLK = 1, nRST;

  // clock
  always #(PERIOD/2) CLK++;

  // interface
  system_if                           syif();
//  datapath_cache_if                   dcif();
  logic flushed;
//  caches_if                           cif();
//  arbiter_caches_if                   acif(cif);
//  scratchpad_if                       spif();
//  systolic_array_if saif();
//  main_mem_if mmif();

  // dut
  system                              DUT (CLK,nRST,flushed,syif);
  // import word type
  import isa_pkg::word_t;
//  import "DPI-C" function void mem_init();

  // number of cycles
  int unsigned cycles = 0;

  initial
  begin
//    mem_init();
    nRST = 0;
     syif.tbCTRL = 0;
     syif.addr = 0;
     syif.store = 0;
     syif.WEN = 0;
     syif.REN = 0;
    @(posedge CLK);
    $display("Starting Scheduler Core:");
    nRST = 1;
    // wait for halt
    while (!flushed)
    begin
      // acif.ramaddr = '1;
      @(posedge CLK);
      cycles++;
    end
    // repeat (100) @(posedge CLK);
    $display("Halted at time = %g and ran for %d cycles.",$time, cycles);
    nRST = 0;
     dump_memory();
    $stop;
  end
  
  task automatic dump_memory();
    string filename;
    int memfd;

    syif.tbCTRL = 1;
    syif.addr = 0;
    syif.store = 0;
    syif.WEN = 0;
    syif.REN = 0;
    
    filename = "/home/asicfab/a/rrbathin/socet/amp/tensor-core/memdump.txt";
    
    memfd = $fopen(filename, "w");
    if (!memfd) begin
        $display("Failed to open %s.", filename);
        $finish;
    end
    $display("Starting memory dump for Scheduler Core.");
    
    for (int unsigned i = 0; i < 1500; i++) begin
        syif.addr = i << 2;
        syif.REN = 1;
        repeat (3) @(posedge CLK);
        $fdisplay(memfd, "%08h", syif.load);
        @(posedge CLK);
    end
    
    syif.tbCTRL = 0;
    syif.REN = 0;
    $fclose(memfd);
    
    $display("Finished memory dump for Scheduler Core.");
  endtask

//      task automatic dump_memory();
//       string filename = "memdump.txt";   // name as you like
//       int memfd;
    
//       syif.tbCTRL = 1;
//       syif.addr = 0;
//       syif.WEN = 0;
    
//       memfd = $fopen(filename, "w");
//       if (!memfd) begin
//         $display("Failed to open %s.", filename);
//         $finish;
//       end
//       $display("Starting memory dump for Scheduler Core.");
    
//       for (int unsigned i = 0; i < 106384; i++) begin
//         syif.addr = i << 2;
//         syif.REN = 1;
//         repeat (3) @(posedge CLK);
    
// //        if (syif.load === 0)
// //          continue;  // skip if load is zero, or remove this if you want to dump zeros too
    
//         $fdisplay(memfd, "%08h", syif.load);  // output as 8-character hex, one per line
//         @(posedge CLK);
//       end
    
//       syif.tbCTRL = 0;
//       syif.REN = 0;
//       $fclose(memfd);
    
//       $display("Finished memory dump for Scheduler Core.");
//     endtask

   
endmodule