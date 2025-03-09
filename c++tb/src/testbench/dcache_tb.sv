// mapped needs this
`include "cache_control_if.vh"
`include "cpu_ram_if.vh"
`include "caches_if.vh"
`include "cpu_types_pkg.vh"
`include "datapath_cache_if.vh"
// mapped timing needs this. 1ns is too fast
`timescale 1 ns / 1 ns

module dcache_tb;
  import "DPI-C" function void mem_init();
  import "DPI-C" function void mem_read(input bit [31:0] address, output bit [31:0] data);
  import "DPI-C" function void mem_write(input bit [31:0] address, input bit [31:0] data);
  import "DPI-C" function void mem_save();
  // clock period
  parameter PERIOD = 20;

  // signals
  logic CLK = 1, nRST;

  // clock
  always #(PERIOD/2) CLK++;


  // interface
  datapath_cache_if dcif();
  caches_if cif0();   
  // test program
  test PROG (CLK,dcif,cif0,nRST);  
  // DUT
  dcache  DUT_dcache(CLK,nRST, dcif, cif0);


endmodule

program test(input logic CLK,datapath_cache_if.cache my_dcif, caches_if my_cif0, output logic nrst); 
int test_num;
  import "DPI-C" function void mem_init();
  import "DPI-C" function void mem_read(input bit [31:0] address, output bit [31:0] data);
  import "DPI-C" function void mem_write(input bit [31:0] address, input bit [31:0] data);
  import "DPI-C" function void mem_save();
  import cpu_types_pkg::*;
  task reset_dut;
  begin
    // Activate the design's reset (does not need to be synchronize with clock)
    nrst = 1'b0;
    // write ('0, '0, '0, '0, '0, '1, '0, '0, '0, '0);
    // Wait for a couple clock cycles
    @(posedge CLK);
    
    // Release the reset
    @(negedge CLK);
    nrst = '1;
    
    // Wait for a while before activating the design
    @(posedge CLK);
  end
  endtask

   task write(
        logic   local_halt, local_dmemREN, local_dmemWEN,
        word_t local_dmemaddr, local_dmemstore,
        logic local_dwait,
        word_t local_dload
   );
   begin
        my_dcif.halt = local_halt;
        my_dcif.dmemREN = local_dmemREN;
        my_dcif.dmemWEN = local_dmemWEN;
        my_dcif.dmemaddr = local_dmemaddr;
        my_dcif.dmemstore = local_dmemstore;
        //mem_write(local_dmemaddr, local_dmemstore);

        my_cif0.dwait = local_dwait;
        my_cif0.dload = local_dload;
        #10;
    end
   endtask



    // test
    initial begin
      bit [31:0] read_data;
      mem_init();
      #10;
      test_num = -1;
      reset_dut;
      #10
      // halt, dmemREN, dmemWEN, dmemaddr, dmemstore, dwait, dload
      

   // halt, dmemREN, dmemWEN, dmemaddr, dmemstore, dwait, dload
       test_num = test_num + 1;   // test case 3
      // write test case -- hit first -- it is clean at first
      // check dirty bit
      write('0, '0, '1, 32'b111100, 32'hFEEDCAFE, '1, '0);    // choose 1 as block offset, that row should be come FEEDCAFE, ffffffff and dirty bit 
      #50

      


      test_num = test_num + 1;   // test case 3
      // write test case -- miss -- if it is not dirty -- tag doesn't exist  -- one word should be zero and the other one is BBBBBBBB
      write('0, '0, '1, 32'b100000, 32'hBBBBBBBB, '1, '0); 
      #50


      test_num = test_num + 1;   // test case 3
      // write test case -- miss -- if it is dirty
       write('0, '0, '1, 32'b111100, 32'hAAAAAAAA, '1, '0);     // one word should be  FEEDCAFE and the other one should be AAAAAAAA
      #50
      mem_read(32'b111100, read_data);
      mem_save();
      $display("Data at address 32'b111000: %h", read_data);
      write('0, '0, '1, 32'b111100, 32'hAAAAAAAA, '0, '0);     // one word should be  FEEDCAFE and the other one should be AAAAAAAA
      #50
      mem_read(32'b111100, read_data);
      mem_save();
      $display("Data at address 32'b111000: %h", read_data);
      write('0, '0, '1, 32'b111100, 32'hAAAAAAAA, '1, '0);     // one word should be  FEEDCAFE and the other one should be AAAAAAAA
      #50
      mem_read(32'b111100, read_data);
      mem_save();
      $display("Data at address 32'b111000: %h", read_data);
      write('0, '0, '1, 32'b111100, 32'hAAAAAAAA, '0, '0);     // one word should be  FEEDCAFE and the other one should be AAAAAAAA
      #50
      mem_read(32'b111100, read_data);
      mem_save();
      $display("Data at address 32'b111000: %h", read_data);




      test_num = test_num + 1;  // halt
      write('1, '0, '0, '0, '0, '1, '0); 
      #50

       write('1, '0, '0, '0, '0, '0, '0); 
      #50

       write('1, '0, '0, '0, '0, '1, '0); 
      #50

       write('1, '0, '0, '0, '0, '0, '0); 
      #50

       write('1, '0, '0, '0, '0, '1, '0); 
      #50

       write('1, '0, '0, '0, '0, '0, '0); 
      #50

       write('1, '0, '0, '0, '0, '1, '0); 
      #50

       write('1, '0, '0, '0, '0, '0, '0); 
      #50

       write('1, '0, '0, '0, '0, '1, '0); 
      #50



      // check if hit counter is stored at address 0x3100

      // check in memory after halt if these memory are written
    
      #1000
      $stop;
      

    end
endprogram