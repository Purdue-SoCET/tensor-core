`ifndef FU_ALU_IF_VH
`define FU_ALU_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface fu_alu_if;
  import isa_pkg::*;

  logic negative, overflow, zero;
  logic [3:0] aluop;
  word_t port_a, port_b, port_output;

  modport alu (
    input aluop, port_a, port_b,
    output negative, overflow, port_output, zero
  );

  modport tb (
    input negative, overflow, port_output, zero,
    output aluop, port_a, port_b
  );

endinterface

`endif
