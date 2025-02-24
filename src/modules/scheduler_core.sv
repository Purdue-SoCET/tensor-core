/*
  Chase Johnson
  cyjohnso@purdue.edu

  scheduler core top block
  holds data path components
  and caches
*/

`include "caches_if.vh"
`include "cache_control_if.vh"

module scheduler_core (
  input logic CLK, nrst,
  output logic halt,
  ram_if.cpu scif
);

parameter PC0 = 0;

  // bus interface
  datapath_cache_if                 dcif ();
  // coherence interface
  cache_control_if                  ccif ();
  arbiter_caches_if                 acif();
  scratchpad_if                     spif();

  // map datapath
  sc_datapath                       SC_DP (CLK, nrst, dcif); //scheduler core datapath

  // map caches
  memory_arbiter_basic MEM_ARB(CLK, nRST, acif, spif);

  icache ICACHE(CLK, nRST, dif, /* dispatch_if */, acif);
  dcache DCACHE(CLK, nRST, dcif, /* fu_scalar_ls_if */, cif);
  // scratchpad


  // map coherence
  // memory_control                    CC (CLK, nrst, ccif);

  // interface connections
  assign scif.memaddr = ccif.ramaddr;
  assign scif.memstore = ccif.ramstore;
  assign scif.memREN = ccif.ramREN;
  assign scif.memWEN = ccif.ramWEN;

  assign ccif.ramload = scif.ramload;
  assign ccif.ramstate = scif.ramstate;

  assign halt = dcif.flushed;
endmodule