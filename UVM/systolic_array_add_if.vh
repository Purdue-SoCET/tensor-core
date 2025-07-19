`ifndef SYSTOLIC_ARRAY_ADD_IF_VH
`define SYSTOLIC_ARRAY_ADD_IF_VH

`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

interface systolic_array_add_if;
  // Signals
  logic start;          // MAC unit start signal
  logic [DW-1:0] add_input1;            // Input weight value to be pre-loaded
  logic [DW-1:0] add_input2;          // Input value to be multiplied
  logic [DW-1:0] add_output;     // Input accumulate value from above
  logic value_ready;                // is 1 when the adder is not currently processing an operation

  // add Port for Array
  modport add(
    input  start, add_input1, add_input2,
    output add_output, value_ready
  );
endinterface

`endif
