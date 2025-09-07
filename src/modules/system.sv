/*
  Chase Johnson
  cyjohnso@purdue.edu

  Connects Data Path Together
*/

// system interface
`include "system_if.vh"
//types
`include "isa_types.vh"
`include "datapath_types.vh"
`include "sp_types_pkg.vh"
`include "ram_pkg.vh"
// `include "types_pkg.vh"
// `include "ram_if.vh"
`include "cpu_ram_if.vh"
`include "datapath_cache_if.vh"
`include "caches_if.vh"
`include "arbiter_caches_if.vh"
`include "scratchpad_if.vh"
`include "main_mem_if.vh"



// module system (input logic CLK, nrst, system_if.sys syif);
// module system (input logic CLK, nrst, system_if.sys syif);
module system (
  input logic CLK, nrst,
  output logic flushed,
  system_if.sys syif
);

  datapath_cache_if dcif();
  caches_if cif();
  arbiter_caches_if acif(cif);
  scratchpad_if spif();
  systolic_array_if saif();
  main_mem_if mmif();

  import ram_pkg::*;
  import isa_pkg::*;
  import datapath_pkg::*;
  import sp_types_pkg::*;

  // stopped running
  logic halt;

  logic [3:0] count;
  
  assign flushed = dcif.flushed;

  sc_datapath DP (CLK, nrst, dcif);
  memory_subsystem MS (CLK, nrst, dcif, cif, acif, spif, mmif, syif);
  systolic_array SYS (CLK, nrst, saif);

  always_comb begin
    saif.weight_en = spif.weight_enable;
    saif.input_en = spif.input_enable;
    saif.partial_en = spif.partial_enable;
    saif.row_in_en = spif.weight_input_row_sel;
    saif.row_ps_en = spif.partial_sum_row_sel;
    saif.array_in = spif.weight_input_data;
    saif.array_in_partials = spif.partial_sum_data;
    spif.drained = saif.drained;
    spif.fifo_has_space = saif.fifo_has_space;
    spif.psumout_data = saif.array_output;
    spif.psumout_row_sel_in = saif.row_out;
    spif.psumout_en = saif.out_en;
    spif.instrFIFO_wdata = dcif.sp_out;
    spif.instrFIFO_WEN = dcif.sp_write;
    dcif.load_complete = spif.load_complete;
    dcif.gemm_complete = spif.gemm_complete;
    dcif.store_complete = spif.store_complete;
  end

  assign syif.halt = dcif.halt;

  // initial 
	// begin: IICE_UC_1
  //   $dumpvars(1, system.CLK);
  //   $dumpvars(1, system.nrst);
  //   $dumpvars(1, system.flushed);
  //   $dumpvars(1, system.MS.acif.ramload);
  //   $dumpvars(1, system.MS.mmif.addr);
  //   $dumpvars(1, system.MS.mmif.data_in);
  //   $dumpvars(1, system.MS.mmif.write_en);
  // end


endmodule