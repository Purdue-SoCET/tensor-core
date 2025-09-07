`ifndef ARBITER_CACHES_IF_VH
`define ARBITER_CACHES_IF_VH

// ram memory types
`include "caches_pkg.vh"
`include "caches_if.vh"

interface arbiter_caches_if(
  caches_if cif
);
  // import types
  import caches_pkg::*;

  // arbitration
  logic   iwait, dwait, iREN, dREN, dWEN, load_done, store_done;
  word_t  iload, dload, dstore;
  word_t  iaddr, daddr;
 
  // ram
  logic                   ramWEN, ramREN, ramBUSY;
  ramstate_t              ramstate;
  word_t                  ramaddr, ramstore, ramload;

  // Connect cache inputs to cif signals
  assign iREN = cif.iREN;
  assign dREN = cif.dREN;
  assign dWEN = cif.dWEN;
  assign dstore = cif.dstore;
  assign iaddr = cif.iaddr;
  assign daddr = cif.daddr;

  // Connect cache outputs to cif signals
  assign cif.iwait = iwait;
  assign cif.dwait = dwait;
  assign cif.iload = iload;
  assign cif.dload = dload;

  // controller ports to ram and caches
  modport cc (
      // cache inputs
      input   iREN, dREN, dWEN, dstore, iaddr, daddr,
      // ram inputs
      input   ramload, ramstate, ramBUSY,
      // cache outputs
      output  iwait, dwait, iload, dload,
      // ram outputs
      output  ramstore, ramaddr, ramWEN, ramREN,
      // dcache outputs
      output  load_done, store_done
      // icache outputs
  );

  modport dcache (
    input load_done, store_done
  );

endinterface

`endif //ARBITER_CACHES_IF_VH