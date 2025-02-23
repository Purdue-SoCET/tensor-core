/*
  Chase Johnson
  cyjohnso@purdue.edu

  scheduler core top block
  holds data path components
  and caches
*/

module scheduler_core (
  input logic CLK, nrst,
  output logic halt,
  cpu_ram_if.cpu scif
);

parameter PC0 = 0;

  // bus interface
  datapath_cache_if                 dcif ();
  // coherence interface
  caches_if                         cif0();
  // cif1 will not be used, but ccif expects it as an input
  caches_if                         cif1();
  cache_control_if #(.CPUS(1))      ccif (cif0, cif1);

  // map datapath
  sc_datapath #(.PC_INIT(PC0))      SC_DP (CLK, nrst, dcif); //scheduler core datapath
  // map caches
  caches                            CM (CLK, nrst, dcif, cif0);
  // map coherence
  memory_control                    CC (CLK, nrst, ccif);

  // interface connections
  assign scif.memaddr = ccif.ramaddr;
  assign scif.memstore = ccif.ramstore;
  assign scif.memREN = ccif.ramREN;
  assign scif.memWEN = ccif.ramWEN;

  assign ccif.ramload = scif.ramload;
  assign ccif.ramstate = scif.ramstate;

  assign halt = dcif.flushed;
endmodule