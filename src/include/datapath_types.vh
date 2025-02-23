`ifndef TYPES_PKG_VH
`define TYPES_PKG_VH

`include "isa_types.vh"

package datapath_pkg;
  import isa_pkg::*;

  parameter FU_W   = 3;
  parameter FU_S_W = 2;
  parameter FU_M_W = 2;

  typedef logic [FU_W-1:0]   fu_bits_t;
  typedef logic [FU_S_W-1:0] fu_sbits_t;
  typedef logic [FU_M_W-1:0] fu_mbits_t;
 
  typedef enum logic [1:0] {
    scalar_na = 2'd0,
    STORE = 2'd2,
    LOAD = 2'd3
  } scalar_mem_t;

  typedef enum logic [1:0] {
    FU_S_T,
    FU_M_T,
    FU_G_T
  } fu_type;

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
  
  /**************
    FUST Structs
  **************/
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

  typedef enum logic [1:0] {
    FU_S_ALU    = 2'd0,
    FU_S_LD_ST  = 2'd1,
    FU_S_BRANCH = 2'd2,
    FU_NONE     = 2'd3
  } fu_scalar_t;

  typedef enum logic [2:0] {
    matrix_na = 3'd0,
    FU_M_LD_ST  = 3'd3,
    FU_M_GEMM   = 3'd4
  } fu_matrix_t;

  typedef struct packed {
    regbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    word_t imm; //instr[31:7] TO: double check this is right 
    fu_sbits_t t1;
    fu_sbits_t t2;
  } fust_s_row_t;

  typedef struct packed {
    logic [2:0] busy;
    fust_s_row_t [2:0] op;
  } fust_s_t;

  typedef struct packed {
    matbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    logic [10:0] imm;
    fu_mbits_t t1;
    fu_mbits_t t2;
    // fu_sbits_t t3;
  } fust_m_row_t;

  typedef struct packed {
    logic busy;
    fust_m_row_t op;
  } fust_m_t;

  typedef struct packed {
    matbits_t rd;
    matbits_t ms1;
    matbits_t ms2;
    matbits_t ms3;
    fu_mbits_t t1;
    fu_mbits_t t2;
    fu_mbits_t t3;
  } fust_g_row_t;

  typedef struct packed {
    logic busy;
    fust_g_row_t op;
  } fust_g_t;

  /*************
    RST Structs
  *************/
  typedef struct packed {
    logic [1:0] tag;
    logic busy;
  } rst_s_row_t;

  typedef struct packed {
    rst_s_row_t [WORD_W-1:0] idx; 
  } rst_s_t;

  typedef struct packed {
    logic [1:0] tag;
    logic busy;
  } rst_m_row_t;

  typedef struct packed {
    rst_m_row_t [15:0] idx; 
  } rst_m_t;

  /*******
    FETCH
  *******/
  typedef struct packed {
    word_t imemload;
  } fetch_t;

  /******************
    CONTROL WRAPPERS
  ******************/
  typedef struct packed {
    // Scalar
    word_t imm;

    // only ALU
    aluop_t alu_op;  

    // only BRANCH
    branch_t branch_op;  

    // only Scalar LDST
    scalar_mem_t s_mem_type;

    // Matrix
    matbits_t m_rw;
    logic m_rw_en;
    matrix_mem_t m_mem_type;

    // only Matrix LDST?
    // only GEMM?
  } ex_ctr_t;

  // output for Writeback.sv
  typedef struct packed {
    logic s_rw_en;
    regbits_t s_rw;
    logic m_rw_en;
    matbits_t m_rw; // still need m_rw in wb for dispatch loopback to clear RST
  } wb_ctr_t;

  typedef struct packed {
    logic s_rw_en;  // scalar read write reg enable
    regbits_t s_rw; // scalar read write register
    logic [WORD_W-1:0] s_wdata; //empty until execute (write data)
    logic load_done;  // Load Done Signal for Score Board
    logic alu_done;   // Alu Done Signal for Score Board
  } wb_t;

  /**********
    DISPATCH
  **********/
  typedef struct packed {
    // Issue signals
    fu_scalar_t fu_s;
    fu_matrix_t fu_m;
    fust_m_t fust_m;
    fust_g_t fust_g;
    fust_s_t fust_s;

    ex_ctr_t ex_ctr;
    wb_ctr_t wb_ctr;
  } dispatch_t;

  /*******
    ISSUE
  *******/
  typedef struct packed {
    fu_bits_t fu_en;
    word_t rdat1;
    word_t rdat2;
    matbits_t ms1;
    matbits_t ms2;
    matbits_t ms3;
  } issue_t;

  typedef struct packed {
    // Branch FU
    logic bfu_pred_outcome;
    logic bfu_hit;
    word_t bfu_pred_target;
    
    // Scalar ALU FU
    logic salu_negative;
    logic salu_overflow;
    word_t salu_port_output;
    logic salu_zero;
    
    // Scalar Load/Store FU
    word_t sls_dmemaddr;
    logic sls_dmemREN;
    logic sls_dmemWEN;
    word_t sls_dmemstore;
    word_t sls_dmemload;
    logic sls_dhit;
    
    // MLS FU
    logic mls_done;
    logic [1:0] mls_ls_out;
    logic [4:0] mls_rd_out;
    word_t mls_address;
    word_t mls_stride_out;
    
    // Gemm FU
    word_t gemm_rs1;
    word_t gemm_rs2;
    word_t gemm_rs3;
    word_t gemm_rd;
  } eif_output_t;

  typedef struct packed {
    logic           done;       // Done signal to Issue Queue
    logic [1:0]     ls_out;     // Load or store to Scratchpad [Load, Store]
    logic [3:0]     rd_out;     // Matrix Reg destination (to Scratchpad)
    logic [10:0]    imm_out;    // Immediate to Scratchpad
    word_t          address;    // Address to Scratchpad
    word_t          stride_out; // stride value
  } matrix_ls_t;

endpackage
`endif
