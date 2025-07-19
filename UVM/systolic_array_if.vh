`ifndef SYSTOLIC_ARRAY_IF_VH
`define SYSTOLIC_ARRAY_IF_VH

`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

interface systolic_array_if(input logic clk);

  // Signals
  logic weight_en;        // Current input bus is for array weights
  logic input_en;         // Current input bus is for array inputs
  logic partial_en;       // Memory is sending partial sums
  logic out_en;
  logic drained;          // Indicates the systolic array is fully drained
  logic fifo_has_space;   // Indicates FIFO has space for another GEMM
  logic [$clog2(N)-1:0] row_in_en;          // Row enable for inputs/weights & partial sums
  logic [$clog2(N)-1:0] row_ps_en;          // Row enable for partial sums
  logic [$clog2(N)-1:0] row_out;            // Which row the systolic array is outputing
  logic [DW*N-1:0] array_in;            // Input data for the array
  logic [DW*N-1:0] array_in_partials;   // Input partial sums for the array
  logic [DW*N-1:0] array_output;        // Output data from the array

  // Memory Ports
  //memory to systolic array
  modport memory_array (  
    input  weight_en, input_en, partial_en, row_in_en, row_ps_en, array_in, array_in_partials,
    output drained, fifo_has_space, row_out, array_output, out_en, clk
  );
  //systolic array to memory
  modport array_memory(   
    input drained, fifo_has_space, row_out, array_output, out_en,
    output weight_en, input_en, partial_en, row_in_en, row_ps_en, array_in, array_in_partials
  );
endinterface

`endif
