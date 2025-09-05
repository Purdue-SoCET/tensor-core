// Each FU have its own modport or interface??
`ifndef VECTOR_IF_VH
`define VECTOR_IF_VH

`include "vector_types.vh"

interface vector_if;
  import vector_pkg::*;

  // Scheduler Core Interface Signals

  // Scratchpad Interface Signals

  // VALU Signals
  fp16_t vdat1, vdat2, result;
  valu_op_t vop;
  /*
  modport vector (
    input 
    output 
  );
  */

  modport valu (
    input vdat1, vdat2, vop,
    output result
  );

endinterface

`endif