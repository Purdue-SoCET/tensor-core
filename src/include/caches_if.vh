`ifndef CACHES_IF_VH
`define CACHES_IF_VH

// ram memory types
`include "caches_pkg.vh"

interface caches_if;

  // import types
  import caches_pkg::*;

  // arbitration
  logic          iwait, dwait, iREN, dREN, dWEN;
  logic[63:0]         iload, dload, dstore;
  word_t         iaddr, daddr;

  // icache ports to controller
  modport icache (
    input   iwait, iload,
    output  iREN, iaddr
  );

  // dcache ports to controller
  modport dcache (
    input   dwait, dload,
    output  dREN, dWEN, daddr, dstore
  );

  // caches ports to controller
  modport caches(
    input   dwait, dload,
            iwait, iload,
    output  dREN, dWEN, daddr, dstore,
            iREN, iaddr
  );


endinterface

`endif //CACHES_IF_VH
