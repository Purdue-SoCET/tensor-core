// `ifndef FU_BRANCHPRED_IF_VH
// `define FU_BRANCHPRED_IF_VH

`include "cpu_types.vh"

interface fu_branchpred_if;
  import cpu_types::*;

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

// `endif