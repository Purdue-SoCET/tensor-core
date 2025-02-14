`ifndef FETCH_BRANCH_IF_VH
`define FETCH_BRANCH_IF_VH
`include "types_pkg.vh"
`include "datapath_types.vh"

interface fetch_branch_if;
  import types_pkg::*;
  import datapath_pkg::*;

  word_t reg_a, reg_b, current_pc, updated_pc, imm;
  logic [1:0] branch_type;
  logic branch, branch_gate_sel, branch_outcome; 
  word_t fetch_load;
  //have to add the rest of the logic for the fetch stage, once its done

  modport fb (
    input branch, branch_type, branch_gate_sel, reg_a, reg_b, current_pc, imm,
    output branch_outcome, updated_pc, fetch_load
  );

  modport tb (
    input branch_outcome, updated_pc, fetch_load,
    output branch, branch_type, branch_gate_sel, reg_a, reg_b, current_pc, imm
  );
  
endinterface
`endif

