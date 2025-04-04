`ifndef DATAPATH_CACHE_IF_VH
`define DATAPATH_CACHE_IF_VH

// types
`include "isa_types.vh"
`include "datapath_types.vh"

interface datapath_cache_if;
  // import types
  import isa_pkg::*;
  import datapath_pkg::*;

// datapath signals
  // stop processing
  logic               halt;

// Icache signals
  // hit and enable
  logic               ihit, imemREN;
  // instruction addr
  word_t             imemload, imemaddr;

// Dcache signals
  // hit, atomic and enables
  logic               dhit, datomic, dmemREN, dmemWEN, flushed;
  // data and address
  word_t              dmemload, dmemstore, dmemaddr;

// Scratchpad signals
  logic mhit;
  matrix_ls_t         matrix_ls;
  logic gemm_done;

  // logic gemm_done;
  scratch_input_t gemm_out; 

  // datapath ports
  modport dp (
    input   ihit, imemload, dhit, dmemload, mhit, gemm_done,
    output  halt, imemREN, imemaddr, dmemREN, dmemWEN,
            dmemstore, dmemaddr, matrix_ls, gemm_out
  );

  modport tb (
    output   ihit, imemload, dhit, dmemload, mhit, gemm_done,
    input  halt, imemREN, imemaddr, dmemREN, dmemWEN,
            dmemstore, dmemaddr, matrix_ls, gemm_out
  );

  // cache block ports
  modport cache (
    input   halt, imemREN, dmemREN, dmemWEN, datomic,
            dmemstore, dmemaddr, imemaddr,
    output  ihit, dhit, imemload, dmemload, flushed
  );

  // icache ports
  modport icache (
    input   imemREN, imemaddr,
    output  ihit, imemload
  );

  // dcache ports
  modport dcache (
    input   halt, dmemREN, dmemWEN,
            datomic, dmemstore, dmemaddr,
    output  dhit, dmemload, flushed
  );
endinterface

`endif //DATAPATH_CACHE_IF_VH