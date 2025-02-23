`ifndef EXECUTE_IF_VH
`define EXECUTE_IF_VH
`include "cpu_types_pkg.vh"
`include "datapath_types.vh"

interface execute_if;
  import datapath_pkg::*; 
  import isa_pkg::*;

  // outputs: next_pc, mispredict, rw_daata, wb_select 
  // CAM_Lookup??
  // SB outputs: fetch, flush, freeze, wb, s_wdata,
  // SB inputs: drained, fifo_has_space, row_out, array_output, out_en
  // SA Inputs:  drained, fifo_has_space, row_out, array_output, out_en
  // SA Outputs: weight_en, input_en, partial_en, row_en, array_in, array_in_partials,

  // Branch FU
  logic bfu_branch_outcome, bfu_update_btb, bfu_pred_outcome, ihit;
  word_t bfu_pc, bfu_pc_fetch, bfu_branch_target, bfu_pred_target;
  // Scalar ALU FU
  word_t salu_imm, salu_dmemload, salu_dmemaddr, salu_dmem_in, salu_dmemstore, salu_rs1, salu_rs2;
  scalar_mem_t salu_mem_type;
  logic salu_dhit, salu_dmemWEN, salu_dmemREN, salu_dhit_in;
  // Scalar Load/Store FU
  word_t sls_imm, sls_dmemload, sls_dmemaddr, sls_dmem_in, sls_dmemstore, sls_rs1, sls_rs2;
  scalar_mem_t sls_mem_type;
  logic sls_dhit, sls_dmemWEN, sls_dmemREN, sls_dhit_in;
  // MLS FU
  logic           mls_mhit, mls_enable;
  logic [1:0]     mls_ls_in;
  logic [4:0]     mls_rd_in;
  logic [10:0]    mls_imm_in;
  word_t          mls_stride_in, mls_rs_in;
  // Gemm FU
  word_t gemm_rs1, gemm_rs2, gemm_rs3, gemm_rd;
  logic gemm_fetch_p, gemm_flush, gemm_freeze;
  


  modport eif (
    input // Branch FU
          ihit, bfu_branch_outcome, bfu_update_btb, bfu_branch_target, bfu_pc, bfu_pc_fetch,
          // Scalar ALU FU
          salu_aluop, salu_port_a, salu_port_b, imm, 
          // Scalar Load/Store FU
          sls_mem_type, sls_rs1, sls_rs2, sls_dmem_in, sls_dhit_in,    
          // MLS FU
          mls_mhit, mls_enable, mls_ls_in, mls_rd_in, mls_rs_in, mls_rs_in, mls_stride_in, mls_imm_in,
          // GEMM FU
          gemm_fetch_p, gemm_flush, gemm_freeze,
    output eif_output_t
  );

  modport tb (
    input eif_output_t,
    output// Branch FU
          ihit, bfu_branch_outcome, bfu_update_btb, bfu_branch_target, bfu_pc, bfu_pc_fetch,
          // Scalar ALU FU
          salu_aluop, salu_port_a, salu_port_b, imm, 
          // Scalar Load/Store FU
          sls_mem_type, sls_rs1, sls_rs2, sls_dmem_in, sls_dhit_in,    
          // MLS FU
          mls_mhit, mls_enable, mls_ls_in, mls_rd_in, mls_rs_in, mls_rs_in, mls_stride_in, mls_imm_in,
          // GEMM FU
          gemm_fetch_p, gemm_flush, gemm_freeze
  );

endinterface

`endif


// SCratchpad fifo signals
// wen, wdata outpputs for me inputs for fifo
// full output fifo input execute (while its not full you can push data)
// when ouptut is not full WEN is high  (37 bit bus write data)

// 37 bit fifo, MSB (1 = Load, 0 = store), 4 bits for matrix, 32 bit address
// for gemm instr only bottom 16 bits have data, rest is 0
// {2'b(Load1, store2, gemm3), 32'b(address or gemm buffer -> 16 0s), 4'b(matrix_rd), 5'b(stride)}

// {2'b(store?)(load?), 4'd(matrix_rd), 32,d(matrix address)} MATRIX LS
// {2'b11, 4'b(new weight?)000, 16'd0, 16'(gemm select)} GEMM Ops