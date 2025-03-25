// // mapped needs this
// `include "cache_control_if.vh"
// `include "cpu_ram_if.vh"
// `include "caches_if.vh"
// `include "cpu_types_pkg.vh"
// `include "datapath_cache_if.vh"
// // mapped timing needs this. 1ns is too fast
// `timescale 1 ns / 1 ns

// module dcache_tb;

//   // clock period
//   parameter PERIOD = 20;

//   // signals
//   logic CLK = 1, nRST;

//   // clock
//   always #(PERIOD/2) CLK++;


//   // interface
//   datapath_cache_if dcif();
//   caches_if cif0();   
//   // test program
//   test PROG (CLK,dcif,cif0,nRST);  
//   // DUT
//   dcache  DUT_dcache(CLK,nRST, dcif, cif0);


// endmodule

// program test(input logic CLK,datapath_cache_if.cache my_dcif, caches_if my_cif0, output logic nrst); 
// int test_num;

// import cpu_types_pkg::*;

//      task reset_dut;
//   begin
//     // Activate the design's reset (does not need to be synchronize with clock)
//     nrst = 1'b0;
//     write ('0, '0, '0, '0, '0, '1, '0, '0, '0, '0);
//     // Wait for a couple clock cycles
//     @(posedge CLK);
    
//     // Release the reset
//     @(negedge CLK);
//     nrst = '1;
    
//     // Wait for a while before activating the design
//     @(posedge CLK);
//   end
//   endtask

//    task write(
//         logic   local_halt, local_dmemREN, local_dmemWEN,
//         word_t local_dmemaddr, local_dmemstore,
//         logic local_dwait,
//         word_t local_dload,
//         logic local_ccwait, local_ccinv,
//         word_t local_ccsnoopaddr
//    );
//    begin
//         my_dcif.halt = local_halt;
//         my_dcif.dmemREN = local_dmemREN;
//         my_dcif.dmemWEN = local_dmemWEN;
//         my_dcif.dmemaddr = local_dmemaddr;
//         my_dcif.dmemstore = local_dmemstore;

//         my_cif0.dwait = local_dwait;
//         my_cif0.dload = local_dload;
//         my_cif0.ccwait = local_ccwait;
//         my_cif0.ccinv = local_ccinv;
//         my_cif0.ccsnoopaddr = local_ccsnoopaddr;
//     end
//    endtask



//     // test
//     initial begin
//       test_num = -1;
//       reset_dut;
//       #10
//       // halt, dmemREN, dmemWEN, dmemaddr, dmemstore, dwait, dload, ccwait, ccinv, ccsnoop
      
//       // first read will be a miss
//       // check: cif.dREN, cif.daddr, dwait change from 1 to 0 2 times, 
//       //dload has two differnt values because two words need to load two times
//       // after than dhit and dmemload should have values
//       test_num = test_num + 1;   // test case 0
//       write('0, '1, '0, 32'b111000, '0, '1, '0, '0, '0, '0);   //cache miss will send dREN
//          @(posedge CLK)

//       // get data from RAM because we only have one cache right now
//       write('0, '1, '0, 32'b111000, '0, '0, 32'hffffffff, '0, '0, '0);  //like a snoopmiss
//       @(posedge CLK)

//       write('0, '1, '0, 32'b111000, '0, '1, '0, '0, '0, '0);
//          @(posedge CLK)

//       write('0, '1, '0, 32'b111000, '0, '0, 32'hffffffff, '0, '0, '0);

//        @(posedge CLK)
//        @(posedge CLK)



//       //now this cache is in shared state
//       // what will happen if other cache snoop it? nothing
//       test_num = test_num + 1;   // test case 1
//       write('0, '0, '1, 32'b111000, 32'hABABABAB, '1, '0, '1, '0, 32'b111000);   //stays at shared state, don't write becasue of ccwait
//        @(posedge CLK)
//         @(posedge CLK)








//       // second read in the cache should result a dhit and dmemload immediately
//        test_num = test_num + 1;   // test case 2
//       write('0, '1, '0, 32'b111000, '0, '1, '0, '0, '0, '0);   //no dREN stays at idle
//        @(posedge CLK)
//        write('0, '0, '0, 32'b111000, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)





//       // same index different tags? should be miss
//       // do the same thing in test 3
//       test_num = test_num + 1;   // test case 0
//       write('0, '1, '0, 32'b0111111000, '0, '1, '0, '0, '0, '0);
//        @(posedge CLK)

//       write('0, '1, '0, 32'b0111111000, '0, '0, 32'hFEEDCAFE, '0, '0, '0);
//        @(posedge CLK)

//       write('0, '1, '0, 32'b0111111000, '0, '1, '0, '0, '0, '0);
//        @(posedge CLK)

//       write('0, '1, '0, 32'b0111111000, '0, '0, 32'hFEEDCAFE, '0, '0, '0);
//        @(posedge CLK)
//        @(posedge CLK)
      

//    // halt, dmemREN, dmemWEN, dmemaddr, dmemstore, dwait, dload, ccwait, ccinv, ccsnoop
//        test_num = test_num + 1;   // test case 4
//       // write test case -- hit first -- it is clean at first
//       // check dirty bit
//       //from shared state to modified
//       write('0, '0, '1, 32'b111000, 32'hFEEDCAAA, '1, '0, '0, '0, '0);    // choose 1 as block offset, that row should be come FEEDCAFE, ffffffff and dirty bit 
//        @(posedge CLK)
//       //should send ccwrite
      

//       test_num = test_num + 1;
//       //TEST CASE 5
//       //what will happen if other cache snoop it? Snoop Hit
//       write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, '1, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        @(posedge CLK)
//        @(posedge CLK)
//        write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, 0, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, 1, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, 0, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        write('0, '0, 0, 32'b111100000000, 32'hBBBBBBBB, 1, '0, 0, '0,  32'b111000);   
//        @(posedge CLK)
//        @(posedge CLK)

//       // from modified to shared state

      


//       test_num = test_num + 1;   // test case 6
//       // write test case -- miss 
//        write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '1, '0, '0, '0, '0);   
//        @(posedge CLK)

//       write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '0, '0, '0, '0, '0);    
//        @(posedge CLK)

//       write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '1, '0, '0, '0, '0);     
//        @(posedge CLK)

//       write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '0, '0, '0, '0, '0);    
//        @(posedge CLK)
//         @(posedge CLK)

//     test_num = test_num + 1;   // test case 7
//       //be sent invalid
//        write('0, '0, '1, 32'b111100, 32'hAAAAAAAA, '1, '0, '1, '1, '0);   
//        @(posedge CLK)
//        write('0, '0, 0, 32'b111100, 32'hAAAAAAAA, '1, '0, 0, 0, '0);   
//        @(posedge CLK)


//       test_num = test_num + 1;  // halt testcase 8
//       write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)
//       //write the dirty data to RAM 2 blocks four words

//       // check if hit counter is stored at address 0x3100

//       // check in memory after halt if these memory are written
    
//       #1000
//       $finish;
      

//     end
// endprogram


// mapped needs this
`include "cache_control_if.vh"
`include "cpu_ram_if.vh"
`include "caches_if.vh"
`include "cpu_types_pkg.vh"
`include "datapath_cache_if.vh"
// mapped timing needs this. 1ns is too fast
`timescale 1 ns / 1 ns

module dcache_tb;

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

import cpu_types_pkg::*;

     task reset_dut;
  begin
    // Activate the design's reset (does not need to be synchronize with clock)
    nrst = 1'b0;
    write ('0, '0, '0, '0, '0, '1, '0, '0, '0, '0);
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
        word_t local_dload,
        logic local_ccwait, local_ccinv,
        word_t local_ccsnoopaddr
   );
   begin
        my_dcif.halt = local_halt;
        my_dcif.dmemREN = local_dmemREN;
        my_dcif.dmemWEN = local_dmemWEN;
        my_dcif.dmemaddr = local_dmemaddr;
        my_dcif.dmemstore = local_dmemstore;

        my_cif0.dwait = local_dwait;
        my_cif0.dload = local_dload;
        my_cif0.ccwait = local_ccwait;
        my_cif0.ccinv = local_ccinv;
        my_cif0.ccsnoopaddr = local_ccsnoopaddr;
    end
   endtask



    // test
    initial begin
      test_num = -1;
      reset_dut;
      #10
      // halt, dmemREN, dmemWEN, dmemaddr, dmemstore, dwait, dload, ccwait, ccinv, ccsnoop
      
      // first read will be a miss
      // check: cif.dREN, cif.daddr, dwait change from 1 to 0 2 times, 
      //dload has two differnt values because two words need to load two times
      // after than dhit and dmemload should have values
//       test_num = test_num + 1;   // test case 0
//       write('0, '1, '0, 32'b111000, '0, '1, '0, '0, '0, '0);   //cache miss will send dREN
//          @(posedge CLK)

//       // get data from RAM because we only have one cache right now
//       write('0, '1, '0, 32'b111000, '0, '0, 32'hffffffff, '0, '0, '0);  //like a snoopmiss
//       @(posedge CLK)

//       write('0, '1, '0, 32'b111000, '0, '1, '0, '0, '0, '0);
//          @(posedge CLK)

//       write('0, '1, '0, 32'b111000, '0, '0, 32'hffffffff, '0, '0, '0);

//        @(posedge CLK)
//        @(posedge CLK)



//       //now this cache is in shared state
//       // what will happen if other cache snoop it? nothing
//       test_num = test_num + 1;   // test case 1
//       write('0, '0, '1, 32'b111000, 32'hABABABAB, '1, '0, '1, '0, 32'b111000);   //stays at shared state, don't write becasue of ccwait
//        @(posedge CLK)
//         @(posedge CLK)








//       // second read in the cache should result a dhit and dmemload immediately
//        test_num = test_num + 1;   // test case 2
//       write('0, '1, '0, 32'b111000, '0, '1, '0, '0, '0, '0);   //no dREN stays at idle
//        @(posedge CLK)
//        write('0, '0, '0, 32'b111000, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)





//       // same index different tags? should be miss
//       // do the same thing in test 3
//       test_num = test_num + 1;   // test case 0
//       write('0, '1, '0, 32'b0111111000, '0, '1, '0, '0, '0, '0);
//        @(posedge CLK)

//       write('0, '1, '0, 32'b0111111000, '0, '0, 32'hFEEDCAFE, '0, '0, '0);
//        @(posedge CLK)

//       write('0, '1, '0, 32'b0111111000, '0, '1, '0, '0, '0, '0);
//        @(posedge CLK)

//       write('0, '1, '0, 32'b0111111000, '0, '0, 32'hFEEDCAFE, '0, '0, '0);
//        @(posedge CLK)
//        @(posedge CLK)
      

//    // halt, dmemREN, dmemWEN, dmemaddr, dmemstore, dwait, dload, ccwait, ccinv, ccsnoop
//        test_num = test_num + 1;   // test case 4
//       // write test case -- hit first -- it is clean at first
//       // check dirty bit
//       //from shared state to modified
//       write('0, '0, '1, 32'b111000, 32'hFEEDCAAA, '1, '0, '0, '0, '0);    // choose 1 as block offset, that row should be come FEEDCAFE, ffffffff and dirty bit 
//        @(posedge CLK)
//       //should send ccwrite
      

//       test_num = test_num + 1;
//       //TEST CASE 5
//       //what will happen if other cache snoop it? Snoop Hit
//       write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, '1, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        @(posedge CLK)
//        @(posedge CLK)
//        write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, 0, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, 1, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        write('0, '0, '1, 32'b111100000000, 32'hBBBBBBBB, 0, '0, '1, '0,  32'b111000);   
//        @(posedge CLK)
//        write('0, '0, 0, 32'b111100000000, 32'hBBBBBBBB, 1, '0, 0, '0,  32'b111000);   
//        @(posedge CLK)
//        @(posedge CLK)

//       // from modified to shared state

      


//       test_num = test_num + 1;   // test case 6
//       // write test case -- miss 
//        write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '1, '0, '0, '0, '0);   
//        @(posedge CLK)

//       write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '0, '0, '0, '0, '0);    
//        @(posedge CLK)

//       write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '1, '0, '0, '0, '0);     
//        @(posedge CLK)

//       write('0, '0, '1, 32'b101010101111100, 32'hAAAAAAAA, '0, '0, '0, '0, '0);    
//        @(posedge CLK)
//         @(posedge CLK)

//     test_num = test_num + 1;   // test case 7
//       //be sent invalid
//        write('0, '0, '1, 32'b111100, 32'hAAAAAAAA, '1, '0, '1, '1, '0);   
//        @(posedge CLK)
//        write('0, '0, 0, 32'b111100, 32'hAAAAAAAA, '1, '0, 0, 0, '0);   
//        @(posedge CLK)


//       test_num = test_num + 1;  // halt testcase 8
//       write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '0, '0, '0, '0, '0); 
//        @(posedge CLK)

//        write('1, '0, '0, '0, '0, '1, '0, '0, '0, '0); 
//        @(posedge CLK)
//       //write the dirty data to RAM 2 blocks four words

//       // check if hit counter is stored at address 0x3100

//       // check in memory after halt if these memory are written
    
      #1000
      $finish;
      

    end
endprogram