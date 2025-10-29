`ifndef FU_BRANCH_IF_VH
`define FU_BRANCH_IF_VH

`include "isa_types.vh"

interface fu_branch_if;
  import isa_pkg::*;

  // branch_fu should just take in which of the 6 branch types the instr, extra logic in the sb should be limited to decoding and out of order

  logic enable, branch, branch_outcome; 
  // logic branch_gate_sel; - branch_gate_sel should be based on what the branch type is from the sb
  logic predicted_outcome, misprediction, update_btb, resolved;
  branch_t branch_type; // this should be branch_t type
  word_t reg_a, reg_b, current_pc, imm, updated_pc, correct_pc, update_pc, branch_target;

  modport br (
    input enable, branch, branch_type, reg_a, reg_b, current_pc, imm, predicted_outcome,
    output branch_outcome, updated_pc, misprediction, correct_pc, update_btb, update_pc, branch_target, resolved
  );

  modport tb (
    output enable, branch, branch_type, reg_a, reg_b, current_pc, imm, predicted_outcome,
    input branch_outcome, updated_pc, misprediction, correct_pc, update_btb, update_pc, branch_target, resolved
  );
endinterface

`endif
