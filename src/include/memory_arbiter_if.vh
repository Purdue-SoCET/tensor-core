/*
  William Wong
  wong371@purdue.edu

  memory arbiter interface signals
*/
`ifndef MEMORY_ARBITER_IF_VH
`define MEMORY_ARBITER_IF_VH

// types
`include "cpu_types_pkg.vh"

interface memory_arbiter_if;
  // import types
  import cpu_types_pkg::*;

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

  // datapath ports
  modport dp (
    input   ihit, imemload, dhit, dmemload,
    output  halt, imemREN, imemaddr, dmemREN, dmemWEN, datomic,
            dmemstore, dmemaddr
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