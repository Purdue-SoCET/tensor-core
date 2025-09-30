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

// mapped timing needs this. 1ns is too fast
`timescale 1 ns / 1 ns

module system_tb;
  // clock period
  parameter PERIOD = 10;

  // signals
  logic CLK = 1, nRST;

  // clock
  always #(PERIOD/2) CLK++;

  // interface
  system_if                           syif();
  datapath_cache_if                   dcif();
  caches_if                           cif();
  arbiter_caches_if                   acif(cif);
  scratchpad_if                       spif();
  systolic_array_if saif();

  // dut
  system                              DUT (CLK,nRST,dcif,cif,acif,spif,saif,syif);
  // import word type
  import isa_pkg::word_t;
  import "DPI-C" function void mem_init();

  // number of cycles
  int unsigned cycles = 0;

  initial
  begin
    mem_init();
    nRST = 0;
    // syif.tbCTRL = 0;
    // syif.addr = 0;
    // syif.store = 0;
    // syif.WEN = 0;
    // syif.REN = 0;
    @(posedge CLK);
    $display("Starting Scheduler Core:");
    nRST = 1;
    // wait for halt
    while (!dcif.flushed)
    begin
      // acif.ramaddr = '1;
      @(posedge CLK);
      cycles++;
    end
    // repeat (100) @(posedge CLK);
    $display("Halted at time = %g and ran for %d cycles.",$time, cycles);
    nRST = 0;
    // dump_memory();
    $stop;
  end

  // task automatic dump_memory();
  //   string filename = "meminit.hex";
  //   int memfd;

  //   syif.tbCTRL = 1;
  //   syif.addr = 0;
  //   syif.WEN = 0;
  //   syif.REN = 0;

  //   memfd = $fopen(filename,"w");
  //   if (memfd)
  //     $display("Starting memory dump for Scheduler Core.");
  //   else
  //     begin $display("Failed to open %s.",filename); $finish; end

  //   for (int unsigned i = 0; memfd && i < 16384; i++)
  //   begin
  //     int chksum = 0;
  //     bit [7:0][7:0] values;
  //     string ihex;

  //     syif.addr = i << 2;
  //     syif.REN = 1;
  //     repeat (4) @(posedge CLK);
  //     if (syif.load === 0)
  //       continue;
  //     values = {8'h04,16'(i),8'h00,syif.load};
  //     foreach (values[j])
  //       chksum += values[j];
  //     chksum = 16'h100 - chksum;
  //     ihex = $sformatf(":04%h00%h%h",16'(i),syif.load,8'(chksum));
  //     $fdisplay(memfd,"%s",ihex.toupper());
  //   end //for
  //   if (memfd)
  //   begin
  //     syif.tbCTRL = 0;
  //     syif.REN = 0;
  //     $fdisplay(memfd,":00000001FF");
  //     $fclose(memfd);
  //     $display("Finished memory dump for Scheduler Core.");
  //   end
  // endtask
endmodule