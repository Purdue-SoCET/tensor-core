`ifndef TYPES_PKG_VH
`define TYPES_PKG_VH

`include "isa_types.vh"

package datapath_pkg;
  import isa_pkg::*;

  parameter FU_W   = 3;
  parameter FU_S_W = 2;
  parameter FU_M_W = 1;

  typedef logic [FU_W-1:0]   fu_bits_t;
  typedef logic [FU_S_W-1:0] fu_sbits_t;
  typedef logic [FU_M_W-1:0] fu_mbits_t;
 
  typedef enum logic [1:0] {
    STORE,
    LOAD,
    MEM_TO_REG
  } scalar_mem_t;

  typedef enum logic {
    M_STORE,
    M_LOAD
  } matrix_mem_t; // load or store for matrix ld_st fu

  typedef enum logic [2:0] {
    FUST_EMPTY,
    FUST_WAIT,
    FUST_RDY,
    FUST_EX
  } fust_state_e;

  typedef struct packed {
    logic busy;
    regbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    logic [24:0] imm; //instr[31:7] TODO: double check this is right 
    fu_sbits_t t1;
    fu_sbits_t t2;
  } fust_s_row_t;

  typedef struct packed {
    fust_s_row_t [FU_S_W-1:0] op;
  } fust_s_t;

  typedef struct packed {
    logic busy;
    matbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    logic [10:0] imm;
    fu_mbits_t t1;
    fu_sbits_t t2;
    fu_sbits_t t3;
  } fust_m_row_t;

  typedef struct packed {
    fust_m_row_t op;
  } fust_m_t;

  typedef struct packed {
    logic busy;
    matbits_t rd;
    matbits_t rs1;
    matbits_t rs2;
    matbits_t rs3;
    fu_mbits_t t1;
    fu_mbits_t t2;
    fu_mbits_t t3;
  } fust_g_row_t;

  typedef struct packed {
    fust_g_row_t op;
  } fust_g_t;

  typedef struct packed {
    logic [1:0] tag;
    logic busy;
  } rst_s_row_t;

  typedef struct packed {
    logic [1:0] tag;
    logic busy;
  } rst_m_row_t;

  typedef struct packed {
    rst_s_row_t [WORD_W-1:0] idx; 
  } rst_s_t;

  typedef struct packed {
    rst_m_row_t [15:0] idx; 
  } rst_m_t;

  // defines the Function Units
  typedef enum logic [2:0] {
    FU_S_ALU    = 3'd0,
    FU_S_LD_ST  = 3'd1,
    FU_S_BRANCH = 3'd2
  } fu_scalar_t;

  typedef enum logic [2:0] {
    FU_M_LD_ST  = 3'd3,
    FU_M_GEMM   = 3'd4
  } fu_matrix_t;

  // Control Signal structs
  typedef struct packed {
    aluop_t alu_op;  
  } fu_alu_ctr_t;

  typedef struct packed {
    branch_t branch_op;  
  } fu_branch_ctr_t;

  typedef struct packed {  
    word_t imm;
    scalar_mem_t mem_type;
  } fu_ldst_ctr_t;
  
  //typedef struct packed {  
    // future double-buffer signals here probably
  //} fu_gemm_ctr_t;

  typedef struct packed {  
    word_t imm;
    matrix_mem_t mem_type;
  } fu_ldst_m_ctr_t;

  typedef struct packed {
    logic s_rw_en;
    regbits_t s_rw;
    logic m_rw_en;
    matbits_t m_rw;
    logic [WORD_W-1:0] s_wdata; //empty until execute
  } wb_t;

  // Pipeline Stage Structs
  typedef struct packed {
    // Issue signals
    fu_scalar_t fu_s;
    fu_matrix_t fu_m;
    fust_m_t fust_m;
    fust_g_t fust_g;
    fust_s_t fust_s;

    fu_alu_ctr_t fu_alu_ctr;
    fu_branch_ctr_t fu_branch_ctr;
    fu_ldst_ctr_t fu_ldst_ctr;
    //fu_gemm_ctr_t fu_gemm_ctr;
    fu_ldst_m_ctr_t fu_ldst_m_ctr;

    wb_t wb;
  } dispatch_t;

  typedef struct packed {
    regbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    fu_alu_ctr_t fu_alu_ctr;
    wb_t wb;
  } fu_alu_t;

  typedef struct packed {
    regbits_t rs1;
    regbits_t rs2;
    fu_branch_ctr_t fu_branch_ctr;
  } fu_branch_t;

  typedef struct packed {
    regbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    fu_ldst_ctr_t fu_ldst_ctr;
    wb_t wb;
  } fu_ldst_t;

  typedef struct packed {
    matbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    fu_ldst_m_ctr_t fu_ldst_m;
    wb_t wb;
  } fu_ldst_m_t;

  typedef struct packed {
    matbits_t rd;
    matbits_t rs1;
    matbits_t rs2;
    matbits_t rs3;
    //fu_gemm_ctr_t fu_gemm_ctr;
  } fu_gemm_t;

  typedef struct packed {
    fu_alu_t fu_alu;
    fu_branch_t fu_branch;
    fu_ldst_t fu_ldst;
    fu_ldst_m_t fu_ldst_m;
    fu_gemm_t fu_gemm;
    fu_bits_t fu_en;
    regbits_t rs1;
    regbits_t rs2;
    matbits_t ms1;
    matbits_t ms2;
    matbits_t ms3;
  } issue_t;

endpackage
`endif
