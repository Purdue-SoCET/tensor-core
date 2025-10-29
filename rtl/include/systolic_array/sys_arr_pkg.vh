`ifndef SYS_ARR_PKG_VH
`define SYS_ARR_PKG_VH

package sys_arr_pkg;
  parameter N = 4; // dimensions of the systolic array
  parameter DW = 16; // data width
  parameter MUL_LEN = 1; // how many cycles to complete a multiply operation
  parameter ADD_LEN = 2; // how many cycles to complete an addition operation
endpackage

`endif
