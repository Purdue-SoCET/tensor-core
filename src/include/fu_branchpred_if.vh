// `ifndef FU_BRANCHPRED_IF_VH
// `define FU_BRANCHPRED_IF_VH

`include "cpu_types.vh"

interface fu_branchpred_if;
  import cpu_types::*;

  logic branch_outcome, update_btb, pred_outcome, hit;
  word_t pc, pc_fetch, branch_target, pred_target;

  modport btb (
    input branch_outcome, update_btb, branch_target, pc, pc_fetch,
    output  pred_outcome, hit, pred_target
  );

  modport tb (
    input  pred_outcome, hit, pred_target,
    output branch_outcome, update_btb, branch_target, pc, pc_fetch
  );
endinterface

// `endif