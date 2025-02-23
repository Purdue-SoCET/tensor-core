`ifndef FU_BRANCH_PREDICTOR_IF_VH
`define FU_BRANCH_PREDICTOR_IF_VH

`include "isa_types.vh"

interface fu_branch_predictor_if;
  import isa_pkg::*;

  logic branch_outcome, update_btb, predicted_outcome;
  word_t pc, update_pc, branch_target, predicted_target;

  modport btb (
    input pc, update_pc, update_btb, branch_outcome, branch_target,
    output  predicted_outcome, predicted_target
  );

  modport tb (
    input  predicted_outcome, predicted_target,
    output pc, update_pc, update_btb, branch_outcome, branch_target
  );
endinterface

`endif