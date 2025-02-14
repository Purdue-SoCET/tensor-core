
`ifndef TYPES_PKG_VH
`define TYPES_PKG_VH

`include "datapath_types.vh"
`include "isa_types.vh"

package types_pkg;
  import datapath_pkg::*;
  // all our instruction params
  parameter WORD_W = 32;
  parameter REG_W  = 5;
  parameter MATRIX_W = 4;

  parameter FU_S_W = 2;
  parameter FU_M_W = 1;

  typedef logic [MATRIX_W-1:0] mbits_t;

  typedef logic [FU_S_W-1:0] fu_sbits_t;
  typedef logic [FU_M_W-1:0] fu_mbits_t;
 
  // defines the Function Units
  typedef enum logic [FU_S_W-1:0] {
    ALU,
    LD_ST,
    BRANCH
  } fu_scalar;

  typedef enum logic [FU_M_W-1:0] {
    M_LD_ST,
    M_GEMM
  } fu_matrix;

  // Pipeline Stage Structs
  typedef struct packed {
    logic hazard;

    // control signals
    
  } dispatch_t;

  // typedef struct packed {
  //   cu_t cu; 
  // } issue_t;

  typedef struct packed {
    logic busy;
    regbits_t r;
    regbits_t r1;
    regbits_t r2;
    fu_sbits_t t1;
    fu_sbits_t t2;
  } fust_s_row_t;

  typedef struct packed {
    fust_s_row_t [FU_S_W-1:0] op;
  } fust_s_t;

  typedef struct packed {
    logic busy;
    mbits_t r;
    mbits_t r1;
    mbits_t r2;
    mbits_t r3;
    fu_mbits_t t1;
    fu_mbits_t t2;
    fu_mbits_t t3;
  } fust_m_row_t;

  typedef struct packed {
    fust_m_row_t [FU_M_W-1:0] op;
  } fust_m_t;

  typedef enum logic [2:0] {
    BT_BEQ, 
    BT_BNE, 
    BT_BLT,
    BT_BGE,
    BT_BLTU,
    BT_BGEU
  } branch_t;

  typedef enum logic [1:0] {
    STORE,
    LOAD
  } scalar_mem_t; 

  typedef enum logic [1:0] {
    M_STORE,
    M_LOAD
  } matrix_mem_t; // load or store for matrix ld_st fu

  typedef enum logic [1:0] {
    UT_LOAD,
    UT_ADD // not using it but here still 
  } utype_t; // what is this ???

endpackage
`endif

