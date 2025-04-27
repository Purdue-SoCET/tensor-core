`ifndef DP_TYPES_PKG_VH
`define DP_TYPES_PKG_VH

`include "isa_types.vh"
`include "sp_types_pkg.vh"

package datapath_pkg;
  import isa_pkg::*;
  import sp_types_pkg::*;

  parameter FU_W   = 5;
  parameter FU_S_W = 2;
  parameter FU_M_W = 2;
  // parameter WORD_W = 32;

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
    M_STORE = 2'd2,
    M_LOAD = 2'd1,
    M_GEMM = 2'd3
  } matrix_mem_t; // Load Store or GEMM from Func Units

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

  typedef enum logic [1:0] {
    dhit_na = 2'd0,
    dhit_load = 2'd1,
    dhit_store = 2'd2
  } dhit_t;

  // typedef enum logic [4:0] {
  //   NA              = 5'b00000,
  //   ALU_DONE        = 5'b00001,
  //   SCALAR_LS_DONE  = 5'b00010,
  //   BRANCH_DONE     = 5'b00100,
  //   MATRIX_LS_DONE  = 5'b01000,
  //   GEMM_DONE       = 5'b10000
  // } fu_done_signals; // scalar stuff for now

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
    logic i_type;
    logic [3:0] op_type;
    scalar_mem_t mem_type;
    logic lui;
    logic [1:0] j_type; // 0(branch) 1(jal) 2(jalr)
  } fust_s_row_t;



  typedef struct packed {
    logic [2:0] busy;
    logic [2:0][1:0] t1;
    logic [2:0][1:0] t2;
    fust_s_row_t [2:0] op;
  } fust_s_t;

  typedef struct packed {
    matbits_t md;
    regbits_t rs1;
    // regbits_t rs2; // stride
    word_t imm;
    matrix_mem_t mem_type;
    // fu_sbits_t t3;
  } fust_m_row_t;

  typedef struct packed {
    logic busy;
    fust_m_row_t op;
    logic [1:0] t1;
  } fust_m_t;

  typedef struct packed {
    matbits_t ms1;
    matbits_t ms2;
    matbits_t ms3;
    matbits_t md;
  } fust_g_row_t;

  typedef struct packed {
    logic busy;
    fust_g_row_t op;
    logic [1:0] t1;
    logic [1:0] t2;
    logic [1:0] t3;
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
    logic m_load_done;
    logic gemm_done;
    matbits_t m_rw_ld;
    matbits_t m_rw_gemm; // still need m_rw in wb for dispatch loopback to clear RST
    // logic load_done;  // Load Done Signal for Score Board
    // logic alu_done;   // Alu Done Signal for Score Board
  } wb_ctr_t; // dispatch

  typedef struct packed {
    logic reg_en;  // scalar read write reg enable
    regbits_t reg_sel; // scalar read write register
    logic [WORD_W-1:0] wdat; //empty until execute (write data)
  } wb_t; // issue

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

    // ex_ctr_t ex_ctr;
    // wb_ctr_t wb_ctr;

    word_t n_br_pc;
    logic n_br_pred;

    logic i_type;
    logic freeze;
    logic spec;
    logic halt;
  } dispatch_t;

  /*******
    ISSUE
  *******/
  typedef struct packed {
    fu_bits_t fu_en; // 0 - alu, 1 - sls, 2 - br, 3 - mls, 4 - gemm
    // alu and lw
    regbits_t rd;
    // br, alu, sls, mls
    word_t rdat1; // mls needs for addr
    word_t rdat2; // mls usees as stride
    word_t imm;   // mls needs for addr 
    // branch
    branch_t branch_type;
    word_t branch_pc;
    logic branch_pred_pc;
    // jump
    logic [1:0] j_type; // 0(branch) 1(jal) 2(jalr)
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
    logic gemm_new_weight;
    
    logic spec;
    logic halt;
  } issue_t;

  typedef struct packed {
    matrix_mem_t mat_op;  // 01 = load, 10 = store, 11 = gemm
    matbits_t mat_rd;   // Normal for L and S, GEMM = {new weight?, 000}
    word_t mat_addr;    
    // Normal for LS, GEMM = {16'0, 16'Gemm_instruction (output weight, input, partial sums)} 
  } scratch_input_t; // issue
  
  typedef struct packed {
    matbits_t rs1;
    matbits_t rs2;
    matbits_t rs3;
    matbits_t rd;
  } fu_gemm_t;

  typedef struct packed {
    logic           done;       // Done signal to Issue Queue
    instrFIFO_t     ls_out;     // Struct to go to the FIFO in the Scratchpad
  } matrix_ls_t;

  typedef struct packed {
    // Branch FU
    logic bfu_branch_outcome;  // to fetch, combinationally
    // word_t bfu_updated_pc;     // to fetch, combinationally
    word_t bfu_correct_pc;     // to fetch, combinationally
    logic bfu_update_btb;      // to fetch, combinationally
    word_t bfu_update_pc;      // to fetch, combinationally
    word_t bfu_branch_target;  // to fetch, combinationally
    logic bfu_resolved;        // to sb and wb, combinationally - correct
    logic bfu_miss;            // to fetch, sb, and wb, combinationally - mispredict
    regbits_t jump_rd;
    // word_t jump_dest;
    word_t jump_wdat;

    // Scalar ALU FU
    logic salu_negative;       // needed?
    logic salu_overflow;       // needed?
    logic salu_zero;           // needed?
    word_t salu_port_output;   // (alu_wdat) to wb thru latch ***
    regbits_t salu_rd;         // (alu_reg_sel) to wb thru latch *** 
    
    // Scalar Load/Store FU
    word_t sls_dmemaddr;       // to mem
    logic sls_dmemREN;         // to mem
    logic sls_dmemWEN;         // to mem
    word_t sls_dmemstore;      // to mem
    word_t sls_dmemload;       // to wb thru latch ***
    dhit_t sls_dhit;           // to sb as done, sls_dhit[0] (load_done) to wb thru latch ***
    regbits_t sls_rd;          // (load_reg_sel) to wb thru latch ***
    
    // MLS FU
    matrix_ls_t fu_matls_out;  // to mem
    
    // Gemm FU
    // logic gemm_new_weight_out; // to mem
    // fu_gemm_t gemm_matrix_num; // to mem
    instrFIFO_t gemm_out;

    logic [4:0] fu_ex; // to sb, fu_ex[0] (alu_done) to wb thru latch ***
    logic spec;
    logic halt;

  } eif_output_t;

  typedef struct packed {
    logic spec;
    // alu wb
    logic alu_done;
    word_t alu_wdat;
    regbits_t alu_reg_sel;

    // lw wb 
    logic load_done;
    word_t load_wdat;
    regbits_t load_reg_sel;

    // jump wb
    logic jump_done;
    word_t jump_wdat;
    regbits_t jump_reg_sel;

  } execute_t;






endpackage
`endif
