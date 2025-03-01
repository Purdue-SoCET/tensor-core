
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
  logic   iwait, dwait, iREN, dREN, dWEN;
  word_t  iload, dload, dstore;
  word_t  iaddr, daddr;
 
  // ram
  logic                   ramWEN, ramREN;
  ramstate_t              ramstate;
  word_t                  ramaddr, ramstore, ramload;

  always_comb begin
      iREN = cif.iREN;
      dREN = cif.dREN;
      dWEN = cif.dWEN;
      dstore = cif.dstore;
      iaddr = cif.iaddr;
      daddr = cif.daddr;

      cif.iwait = iwait;
      cif.dwait = dwait;
      cif.iload = iload;
      cif.dload = dload;
  end

  // controller ports to ram and caches
  modport cc (
            // cache inputs
    input   iREN, dREN, dWEN, dstore, iaddr, daddr,
            // ram inputs
            ramload, ramstate,
            // cache outputs
    output  iwait, dwait, iload, dload,
            // ram outputs
            ramstore, ramaddr, ramWEN, ramREN
  );

endinterface

`endif //ARBITER_CACHES_IF_VH