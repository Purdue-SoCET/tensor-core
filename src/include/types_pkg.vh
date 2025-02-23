`ifndef TYPES_PKG_VH
`define TYPES_PKG_VH

package types_pkg;
  // all our instruction params
  parameter WORD_W = 32;
  parameter REG_W  = 5;
  parameter MATRIX_W = 4;
  parameter VALUE_BITS = 16;
  parameter BITS_PER_ROW = MATRIX_W * VALUE_BITS;

  parameter MAT_S_W = 2;
  parameter ROW_S_W = 2;
  parameter STRIDE = 8;


endpackage
`endif
