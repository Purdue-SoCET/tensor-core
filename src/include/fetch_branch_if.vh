`ifndef FETCH_BRANCH_IF_VH
`define FETCH_BRANCH_IF_VH

`include "isa_types.vh"

interface fetch_branch_if;
 import isa_pkg::*;

  word_t reg_a, reg_b, current_pc, imm, imemload, instr, pc;
  logic [1:0] branch_type;
  logic branch, branch_gate_sel, dispatch_free, flush, stall, predicted_outcome, ihit; 
  //have to add the rest of the logic for the fetch stage, once its done

  modport fb (
    input imemload, flush, stall, dispatch_free, branch, branch_type, branch_gate_sel, reg_a, reg_b, ihit, 
          current_pc, imm, predicted_outcome,
    output instr, pc
  );

  modport tb (
    input pc, instr,
    output imemload, flush, stall, dispatch_free, branch, branch_type, branch_gate_sel, reg_a, reg_b, 
           current_pc, imm, predicted_outcome, ihit
  );
endinterface

`endif

