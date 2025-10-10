// Each FU have its own modport or interface??
`ifndef VECTOR_IF_VH
`define VECTOR_IF_VH

`include "vector_types.vh"

interface vector_if;
  import vector_pkg::*;

  // Top level signals
  logic CLK, nRST;
  /*
  logic CLK, nRST;
  control_t control;
  vreg_t v1, v2, vdata; // FP16 Vector Data
  vsel_t vd;
  logic [NUM_ELEMENTS-1:0] vmask; 
  logic [31:0] r1; 
  logic swizzle, wen;
  logic [11:0] row, col;
  logic [5:0] row_id;
  dtype_t datatype;
  logic [4:0] error;
  logic [IMM_W-1:0] imm;
  
  // Scheduler Core Interface Signals

  // Scratchpad Interface Signals

  // VALU Signals GOING TO DELETE
  vreg_t vdat1, vdat2, result;
  */
  // VEGGIE SIGNALS
  veggie_in_t veggie_in; 
  veggie_out_t veggie_out;
/*
  // Lane Signals 
  lane_in_t lane_in;
  lane_out_t lane_out;
  */
  // Mask Unit Signals
  masku_in_t masku_in;
  masku_out_t masku_out;
/* 
  modport vector (
    input control, r1, imm, vd, v1, v2, vmask, col, row, row_id,
    output wen, vd, vdata, swizzle, col, row, datatype, row_id, error
  );
  // Scoreboard will handle taking imm or
  modport valu (
    input vdat1, vdat2, vop, vmask,
    output result
  );
  */
  // Veggie
  modport veggie (
    input CLK, nRST, 
    input veggie_in,
    output veggie_out
  );
  /*
  // Lane
  modport lane (
    input logic CLK, nRST,
    input lane_in,
    output lane_out
  );  

  modport seq_alu (
    input alut_in,
    output alut_out
  );
  modport alu_wb (
    input aluwb_in,
    output aluwb_out
  );
*/
  modport masku (
    input masku_in,
    output masku_out
  );

endinterface

`endif