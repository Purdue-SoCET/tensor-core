`ifndef FU_BRANCH_IF_VH
`define FU_BRANCH_IF_VH

`include "isa_types.vh"

interface fu_branch_if;
  import isa_pkg::*;

  logic branch, branch_gate_sel, branch_outcome;
  logic predicted_outcome, misprediction, update_btb;
  logic [1:0] branch_type;
  word_t reg_a, reg_b, current_pc, imm, updated_pc, correct_pc, update_pc, branch_target;

  modport br (
    input branch, branch_type, branch_gate_sel, reg_a, reg_b, current_pc, imm, predicted_outcome,
    output branch_outcome, updated_pc, misprediction, correct_pc, update_btb, update_pc, branch_target
  );

  modport tb (
    output branch, branch_type, branch_gate_sel, reg_a, reg_b, current_pc, imm, predicted_outcome,
    input branch_outcome, updated_pc, misprediction, correct_pc, update_btb, update_pc, branch_target
  );
endinterface

`endif
