`ifndef EXECUTE_IF_VH
`define EXECUTE_IF_VH

`include "datapath_types.vh"
`include "isa_types.vh"


// IGNORE
// SCratchpad fifo signals
// wen, wdata outpputs for me inputs for fifo
// full output fifo input execute (while its not full you can push data)
// when ouptut is not full WEN is high  (37 bit bus write data)

// 37 bit fifo, MSB (1 = Load, 0 = store), 4 bits for matrix, 32 bit address
// for gemm instr only bottom 16 bits have data, rest is 0
// {2'b(Load1, store2, gemm3), 32'b(address or gemm buffer -> 16 0s), 4'b(matrix_rd), 5'b(stride)}

// {2'b(store?)(load?), 4'd(matrix_rd), 32,d(matrix address)} MATRIX LS
// {2'b11, 4'b(new weight?)000, 16'd0, 16'(gemm select)} GEMM Ops


interface execute_if;
  import datapath_pkg::*; 
  import isa_pkg::*;

  // Branch FU
  logic bfu_branch, bfu_branch_gate_sel, bfu_branch_outcome;
  logic bfu_predicted_outcome, bfu_misprediction, bfu_update_btb;
  logic [1:0] bfu_branch_type;
  word_t bfu_reg_a, bfu_reg_b, bfu_current_pc, bfu_imm, bfu_updated_pc, bfu_correct_pc, bfu_update_pc, bfu_branch_target;
  // Scalar ALU FU
   word_t salu_port_a, salu_port_b;
   logic [3:0] salu_aluop;
  // Scalar Load/Store FU
  word_t sls_imm, sls_rs1, sls_rs2, sls_dmem_in;
  logic sls_dhit_in;
  scalar_mem_t sls_mem_type;
  // MLS FU
  logic           mls_mhit, mls_enable;
  logic [1:0]     mls_ls_in;
  logic [3:0]     mls_rd_in, mls_rs_in;
  logic [10:0]    mls_imm_in;
  word_t          mls_stride_in;
  // Gemm FU
  logic gemm_enable, gemm_new_weight_in;
  matbits_t gemm_rs1_in, gemm_rs2_in, gemm_rs3_in, gemm_rd_in;
  eif_output_t eif_output;

  modport eif (
    input // Branch FU
          bfu_branch, bfu_branch_type, bfu_branch_gate_sel, bfu_reg_a, bfu_reg_b, bfu_current_pc, bfu_imm, bfu_predicted_outcome,
          // Scalar ALU FU
          salu_aluop, salu_port_a, salu_port_b,
          // Scalar Load/Store FU
          sls_imm, sls_rs1, sls_rs2, sls_dmem_in, sls_dhit_in, sls_mem_type,
          // MLS FU
          mls_mhit, mls_enable, mls_ls_in, mls_rd_in, mls_rs_in, mls_stride_in, mls_imm_in,
          // GEMM FU
          gemm_enable, gemm_new_weight_in, gemm_rs1_in, gemm_rs2_in, gemm_rs3_in, gemm_rd_in,
    output eif_output
  );

  modport tbif (
    input eif_output,
    output// Branch FU
          bfu_branch, bfu_branch_type, bfu_branch_gate_sel, bfu_reg_a, bfu_reg_b, bfu_current_pc, bfu_imm, bfu_predicted_outcome,
          // Scalar ALU FU
          salu_aluop, salu_port_a, salu_port_b,
          // Scalar Load/Store FU
          sls_imm, sls_rs1, sls_rs2, sls_dmem_in, sls_dhit_in, sls_mem_type,
          // MLS FU
          mls_mhit, mls_enable, mls_ls_in, mls_rd_in, mls_rs_in, mls_stride_in, mls_imm_in,
          // GEMM FU
          gemm_enable, gemm_new_weight_in, gemm_rs1_in, gemm_rs2_in, gemm_rs3_in, gemm_rd_in
  );

endinterface

`endif


