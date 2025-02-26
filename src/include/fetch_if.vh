`ifndef FETCH_IF_VH
`define FETCH_IF_VH

`include "isa_types.vh"

interface fetch_if;
  import isa_pkg::*;

  logic flush, stall, dispatch_free, misprediction, ihit;
  word_t imemload, pc_prediction, instr, pc, correct_target, correct_pc;

  modport ft (
    input imemload, flush, stall, dispatch_free, pc_prediction, misprediction, correct_target, correct_pc, ihit,
    output instr, pc
  );

  modport tb (
    input instr, pc,
    output imemload, flush, stall, dispatch_free, pc_prediction, misprediction, correct_target, correct_pc, ihit
  );

endinterface

`endif

`ifndef FETCH_IF_VH
`define FETCH_IF_VH

`include "isa_types.vh"

interface fetch_if;
  import isa_pkg::*;

  logic flush, stall, dispatch_free, misprediction;
  word_t imemload, pc_prediction, instr, pc, correct_target;

  modport ft (
    input imemload, flush, stall, dispatch_free, pc_prediction, misprediction, correct_target,
    output instr, pc
  );

  modport tb (
    input instr, pc,
    output imemload, flush, stall, dispatch_free, pc_prediction, misprediction, correct_target
  );

endinterface

`endif
