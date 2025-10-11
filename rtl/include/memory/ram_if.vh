
`ifndef RAM_IF_VH
`define RAM_IF_VH

`include "ram_pkg.vh"
`include "isa_types.vh"

interface ram_if;
  // import types
  import ram_pkg::*;
  import isa_pkg::*;

  // ram signals
  logic               ramREN, ramWEN;
  word_t              ramaddr, ramstore, ramload;
  ramstate_t          ramstate;

  // cpu signals
  logic               memREN, memWEN;
  word_t              memaddr, memstore;


  // cpu ports
  modport cpu (
    input   ramstate, ramload,
    output  memaddr, memREN, memWEN, memstore
  );

  // ram ports
  modport ram (
    input   ramaddr, ramstore, ramREN, ramWEN,
    output  ramstate, ramload
  );

  // unused and may change
  modport sdram (
    input   ramaddr, ramstore, ramREN, ramWEN,
    output  ramstate, ramload
  );
endinterface

`endif