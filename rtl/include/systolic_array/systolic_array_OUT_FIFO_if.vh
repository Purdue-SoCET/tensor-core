`ifndef SYSTOLIC_ARRAY_OUT_FIFO_IF_VH
`define SYSTOLIC_ARRAY_OUT_FIFO_IF_VH

`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

interface systolic_array_OUT_FIFO_if;

  // Signals
  logic shift;    // FIFO shift signal
  logic [DW-1:0] shift_value;   // next value to push out
  logic [DW*N-1:0] out;           // Final array_dim value to be seen by array
  // Memory Ports
  modport OUT_FIFO(
    input  shift, shift_value, 
    output out
  );
endinterface

`endif
