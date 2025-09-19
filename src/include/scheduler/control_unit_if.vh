`ifndef CONTROL_UNIT_IF_VH
`define CONTROL_UNIT_IF_VH

`include "datapath_types.vh"

interface control_unit_if;

  // import types
  import isa_pkg::*;
  import datapath_pkg::*;

  // logic [5:0] b_type;

  aluop_t alu_op;
  logic [4:0] stride;
  logic halt, i_flag, m_reg_write, s_reg_write, jalr, jal;
  scalar_mem_t s_mem_type;
  branch_t branch_op;
  word_t imm, instr;
  utype_t u_type;
  fu_scalar_t fu_s;
  fu_matrix_t fu_m;
  matrix_mem_t m_mem_type;
  logic [3:0] matrix_rd, matrix_rs1;
  fu_type fu_t;

  modport cu (
    input instr,
    output halt, fu_t, i_flag, s_mem_type, m_reg_write, s_reg_write, jalr, jal, u_type, alu_op, branch_op, imm, stride, fu_s, fu_m, m_mem_type, matrix_rd, matrix_rs1
  );

  modport tb (
    input halt, fu_t, i_flag, s_mem_type, m_reg_write, s_reg_write, jalr, jal, u_type, alu_op, branch_op, imm, stride, fu_s, fu_m, m_mem_type, matrix_rd, matrix_rs1,
    output instr
  );

endinterface
`endif //CONTROL_UNIT_IF_VH
