`ifndef FETCH_IF_VH
`define FETCH_IF_VH

`include "isa_types.vh"

interface fetch_if;
  import isa_pkg::*;

  logic flush, freeze, misprediction;
  word_t imemload, pc_prediction, instr, pc, correct_target, correct_pc;

  modport ft (
    input imemload, flush, freeze, pc_prediction, misprediction, correct_target, correct_pc,
    output instr, pc
  );

  modport tb (
    input instr, pc,
    output imemload, flush, freeze, pc_prediction, misprediction, correct_target, correct_pc
  );

endinterface

`endif
