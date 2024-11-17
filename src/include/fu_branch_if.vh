`ifndef FU_BRANCH_IF_VH
`define FU_BRANCH_IF_VH

`include "types_pkg.vh"

interface fu_alu_if;
  import types_pkg::*;

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

`endif