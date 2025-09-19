/*
  Chase Johnson
  cyjohnso@purdue.edu

  scheduler core top block
  holds data path components
  and caches
*/

`include "caches_if.vh"
`include "cache_control_if.vh"
`include "scratchpad_if.vh"
`include "datapath_cache_if.vh"
`include "arbiter_caches_if.vh"

module scheduler_core (
  input logic CLK, nrst,
  output logic halt,
  ram_if.cpu scif
);

parameter PC0 = 0;

  // bus interface
  datapath_cache_if                 dcif ();
  // coherence interface
  caches_if                         cif ();
  arbiter_caches_if                 acif(cif);
  scratchpad_if                     spif();

  // map datapath
  sc_datapath                       SC_DP (CLK, nrst, dcif); //scheduler core datapath

  // map caches
  memory_arbiter_basic MEM_ARB(CLK, nrst, acif, spif);

  icache ICACHE(CLK, nrst, cif, dcif);
  dcache DCACHE(CLK, nrst, cif, dcif);
  // scratchpad


  // map coherence

  // interface connections
  assign scif.memaddr = acif.ramaddr;
  assign scif.memstore = acif.ramstore;
  assign scif.memREN = acif.ramREN;
  assign scif.memWEN = acif.ramWEN;

  assign acif.ramload = scif.ramload;
  // assign acif.ramstate = scif.ramstate;

  assign halt = dcif.flushed;
endmodule