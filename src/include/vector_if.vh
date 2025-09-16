// Each FU have its own modport or interface??
`ifndef VECTOR_IF_VH
`define VECTOR_IF_VH

`include "vector_types.vh"

interface vector_if;
  import vector_pkg::*;
 
  // Chase: I commentet out some of the signals that were listed in both the inputs and outputs
  // so that I could compile my code for the add/sub module. We can add them back and change the names as needed

  // Top level signals
  logic CLK, nRST;
  control_t control;
  vreg_t v1, v2, vdata; // FP16 Vector Data
  //vsel_t vd;
  logic [NUM_ELEMENTS-1:0] vmask; 
  logic [31:0] r1; 
  logic swizzle, wen;
  //logic [11:0] row, col;
  //logic [5:0] row_id;
  
  dtype_t datatype;
  logic [4:0] error;
  logic [IMM_W-1:0] imm;
  opcode_t vop;

  // Scheduler Core Interface Signals

  // Scratchpad Interface Signals

  // VALU Signals
  vreg_t vdat1, vdat2, result;
  
  modport vector (
    input control, r1, imm, /*vd, */ v1, v2, vmask, /*col, row, row_id, */
    output wen, /*vd, */ vdata, swizzle, /*col, row, */ datatype, /*row_id, */ error
  );
  // Scoreboard will handle taking imm or
  modport valu (
    input vdat1, vdat2, vop, vmask,
    output result
  );

endinterface

`endif