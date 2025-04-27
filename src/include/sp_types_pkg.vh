`ifndef SP_TYPES_PKG_VH
`define SP_TYPES_PKG_VH

`include "isa_types.vh"

  package sp_types_pkg;
  import isa_pkg::*;

  parameter WORD_W = 32;
  parameter REG_W  = 5;
  parameter MATRIX_W = 4;
  parameter VALUE_BITS = 16;
  parameter BITS_PER_ROW = 64;

  parameter MAT_S_W = 4;
  parameter ROW_S_W = 2;
  parameter STRIDE = 8;
  parameter MATS_PER_BANK = 16;
  parameter NUM_BANKS = 4;

  typedef struct packed {
    logic gemm_result;
    logic [MAT_S_W-1:0] mat_s;
    logic [ROW_S_W-1:0] row_s;
    logic [BITS_PER_ROW-1:0] data;
  } wFIFO_t;

  typedef struct packed {
    logic [WORD_W-1:0] addr;
    logic [1:0] mat_t; //00 = store, rest = gemm mat type (order preserved)
    logic [MAT_S_W-1:0] mat_s;
    logic [ROW_S_W-1:0] row_s;
  } rFIFO_t;

  typedef struct packed {
    logic [WORD_W-1:0] addr;
    logic [MAT_S_W-1:0] mat_s;
    logic [ROW_S_W-1:0] row_s;
    logic [BITS_PER_ROW-1:0] data;
  } dramFIFO_t;

  typedef struct packed {
    logic [1:0] mat_t;
    logic [MAT_S_W-1:0] mat_s;
    logic [ROW_S_W-1:0] row_s;
    logic [BITS_PER_ROW-1:0] data;
  } gemmFIFO_t;

  typedef struct packed {
    logic [1:0] opcode;
    matbits_t ls_matrix_rd_gemm_new_weight;
    word_t ls_addr_gemm_gemm_sel;
  } instrFIFO_t;

  /*
    {2'b(store?)(load?), 4'd(matrix_rd), 32,d(matrix address)} MATRIX LS
    {2'b11, 4'b(new weight?)000, 16'd0, 16'(gemm select)} GEMM Ops
  */

  typedef struct packed {
    logic [1:0] row_s;
    logic [BITS_PER_ROW-1:0] data;
  } psumoutFIFO_t;




endpackage
`endif