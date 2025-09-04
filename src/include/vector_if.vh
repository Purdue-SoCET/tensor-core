// Each FU have its own modport or interface??
`ifndef VECTOR_IF_VH
`define VECTOR_IF_VH

`include "isa_types.vh"

interface vector_if;
  import isa_pkg::*;

  // Scheduler Core Interface Signals

  // Scratchpad Interface Signals

  modport vector (
    input 
    output 
  );

  modport tb (
    input 
    output 
  );

endinterface

`endif