`ifndef TYPES_PKG_VH
`define TYPES_PKG_VH

`include "isa_types.vh"

package datapath_pkg;
  import isa_pkg::*;

  parameter FU_W   = 5;
  parameter FU_S_W = 2;
  parameter FU_M_W = 2;

  typedef logic [FU_W-1:0]   fu_bits_t;
  typedef logic [FU_S_W-1:0] fu_sbits_t;
  typedef logic [FU_M_W-1:0] fu_mbits_t;
 
  typedef enum logic [1:0] {
    scalar_na = 2'd0,
    STORE = 2'd1,
    LOAD = 2'd2
  } scalar_mem_t;

  typedef enum logic [1:0] {
    FU_S_T,
    FU_M_T,
    FU_G_T
  } fu_type;

  typedef enum logic [1:0] {
    matrix_na = 2'd0,
    M_STORE = 2'd1,
    M_LOAD = 2'd2
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
    // fu enable from issue
  } fu_alu_ctr_t;

  typedef struct packed {
    branch_t branch_op;  
    // fu enable from issue
  } fu_branch_ctr_t;

  typedef struct packed {  
    word_t imm;
    scalar_mem_t mem_type;
    // fu enable from issue
  } fu_ldst_ctr_t;
  
  // typedef struct packed {  
  //   // future double-buffer signals here probably
  //   // whatever gemm fu needs
  //   // fu_gemm_t the registers (rename to be accurate)
  //   // enable
  // } fu_gemm_ctr_t;

  typedef struct packed {  
    word_t imm;
    matrix_mem_t mem_type;
    // fu enable from issue;
  } fu_ldst_m_ctr_t;

  typedef enum logic [1:0] {
    FU_S_ALU    = 2'd0,
    FU_S_LD_ST  = 2'd1,
    FU_S_BRANCH = 2'd2,
    FU_NONE     = 2'd3
  } fu_scalar_t;

  typedef enum logic [4:0] {
    NA              = 5'b00000,
    ALU_DONE        = 5'b00001,
    SCALAR_LS_DONE  = 5'b00010,
    BRANCH_DONE     = 5'b00100,
    MATRIX_LS_DONE  = 5'b01000,
    GEMM_DONE       = 5'b10000
  } fu_done_signals; // scalar stuff for now

  typedef enum logic [2:0] {
    matrix_fu_na = 3'd0,
    FU_M_LD_ST  = 3'd3,
    FU_M_GEMM   = 3'd4
  } fu_matrix_t;

  typedef struct packed {
    regbits_t rd;
    regbits_t rs1;
    regbits_t rs2;
    word_t imm; //instr[31:7] TODO: double check this is right 
    logic spec;
    logic [3:0] op_type;
    scalar_mem_t mem_type;
  } fust_s_row_t;



  typedef struct packed {
    logic [2:0] busy;
    logic [2:0][1:0] t1;
    logic [2:0][1:0] t2;
    fust_s_row_t [2:0] op;
  } fust_s_t;

  typedef struct packed {
    matbits_t rd;
    regbits_t rs1;
    regbits_t rs2; // stride
    word_t imm;
    fu_mbits_t t1;
    fu_mbits_t t2;
    matrix_mem_t mem_type;
    // fu_sbits_t t3;
  } fust_m_row_t;

  typedef struct packed {
    logic busy;
    fust_m_row_t op;
  } fust_m_t;

  typedef struct packed {
    matbits_t md;
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
    logic spec;
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
    word_t br_pc;
    logic br_pred;
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
    logic load_done;  // Load Done Signal for Score Board
    logic alu_done;   // Alu Done Signal for Score Board
  } wb_ctr_t;

  typedef struct packed {
    logic s_rw_en;  // scalar read write reg enable
    regbits_t s_rw; // scalar read write register
    word_t s_wdata; //empty until execute (write data)
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

    word_t n_br_pc;
    logic n_br_pred;

    logic freeze;

    logic halt;
  } dispatch_t;

  /*******
    ISSUE
  *******/
  typedef struct packed {
    fu_bits_t fu_en; // 0 - alu, 1 - sls, 2 - br, 3 - mls, 4 - gemm
    // br, alu, sls, mls
    word_t rdat1; // mls needs for addr
    word_t rdat2; // mls usees as stride
    word_t imm;   // mls needs for addr 
    // branch
    branch_t branch_type;
    word_t branch_pc;
    logic branch_pred_pc;
    // alu
    aluop_t alu_op;
    // matrix ls
    matrix_mem_t ls_in;
    // scalar ls
    scalar_mem_t mem_type;
    // gemm
    matbits_t md;  // used for m_ls
    matbits_t ms1; 
    matbits_t ms2; 
    matbits_t ms3;

    logic halt;
  } issue_t;


  
  typedef struct packed {
    matbits_t rs1;
    matbits_t rs2;
    matbits_t rs3;
    matbits_t rd;
  } fu_gemm_t;



  typedef struct packed {
    logic           done;       // Done signal to Issue Queue
    matrix_mem_t    ls_out;     // Load or store to Scratchpad [Load, Store]
    matbits_t       rd_out;     // Matrix Reg destination (to Scratchpad)
    word_t          imm_out;    // Immediate to Scratchpad -> needed?
    word_t          address;    // Address to Scratchpad   -> rs_in + imm
    word_t          stride_out; // stride value
  } matrix_ls_t;

  typedef struct packed {
    // Branch FU
    logic bfu_branch_outcome;
    word_t bfu_updated_pc;
    word_t bfu_correct_pc;
    logic bfu_update_btb;
    word_t bfu_update_pc;
    word_t bfu_branch_target;  
    logic bfu_resolved;        // to dp
    logic bfu_misprediction;   // to dp

    // Scalar ALU FU
    logic salu_negative;       // needed?
    logic salu_overflow;       // needed?
    word_t salu_port_output;
    logic salu_zero;           // needed?
    
    // Scalar Load/Store FU
    word_t sls_dmemaddr;       // to mem
    logic sls_dmemREN;         // to mem
    logic sls_dmemWEN;         // to mem
    word_t sls_dmemstore;      // to mem
    word_t sls_dmemload;       // to dp
    logic sls_dhit;            // to dp
    
    // MLS FU
    matrix_ls_t fu_matls_out;  
    
    // Gemm FU
    logic gemm_new_weight_out;
    fu_gemm_t gemm_matrix_num;

  } eif_output_t;


endpackage
`endif
