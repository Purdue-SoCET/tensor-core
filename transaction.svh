`include "sys_arr_pkg.vh"
import sys_arr_pkg::*;

class transaction #(parameter NUM_BITS = 4) extends uvm_sequence_item;
  

  // Signals
  bit weight_en;        // Current input bus is for array weights
  bit input_en;         // Current input bus is for array inputs
  bit partial_en;       // Memory is sending partial sums
  bit out_en;
  bit drained;          // Indicates the systolic array is fully drained
  bit fifo_has_space;   // Indicates FIFO has space for another GEMM
  bit [$clog2(N)-1:0] row_in_en;          // Row enable for inputs/weights & partial sums
  bit [$clog2(N)-1:0] row_ps_en;          // Row enable for partial sums
  bit [$clog2(N)-1:0] row_out;            // Which row the systolic array is outputing
  bit [DW*N-1:0] array_in;            // Input data for the array
  bit [DW*N-1:0] array_in_partials;   // Input partial sums for the array
  bit [DW*N-1:0] array_output;        // Output data from the array
  rand bit [N-1:0][DW*N-1:0] input_matrix;
  rand bit [N-1:0][DW*N-1:0] weight_matrix;
  rand bit [N-1:0][DW*N-1:0] partial_matrix;
  bit [N-1:0][DW*N-1:0] out_matrix;

  `uvm_object_utils_begin(transaction)
    `uvm_field_int(weight_en, UVM_NOCOMPARE)
    `uvm_field_int(input_en, UVM_NOCOMPARE)
    `uvm_field_int(partial_en, UVM_NOCOMPARE)
    `uvm_field_int(row_in_en, UVM_NOCOMPARE)
    `uvm_field_int(row_ps_en, UVM_NOCOMPARE)
    `uvm_field_int(row_out, UVM_NOCOMPARE)
    `uvm_field_int(drained, UVM_NOCOMPARE)
    `uvm_field_int(fifo_has_space, UVM_NOCOMPARE)
    `uvm_field_int(array_in, UVM_NOCOMPARE)
    `uvm_field_int(array_in_partials, UVM_NOCOMPARE)
    `uvm_field_int(out_en, UVM_NOCOMPARE)
    `uvm_field_int(array_output, UVM_NOCOMPARE)
    `uvm_field_int(input_matrix, UVM_DEFAULT)
    `uvm_field_int(weight_matrix, UVM_DEFAULT)
    `uvm_field_int(partial_matrix, UVM_DEFAULT)
    `uvm_field_int(out_matrix, UVM_DEFAULT)
  `uvm_object_utils_end
  // add constrains for randomization

  function new(string name = "transaction");
    super.new(name);
  endfunction: new

  // if two transactions are the same, return 1
  // function int input_equal(transaction tx);
  //   int result;
  //   if((a == tx.a) && (b == tx.b) && (carry_in == tx.carry_in)) begin
  //     result = 1;
  //     return result;
  //   end
  //   result = 0;
  //   return result;
  // endfunction
endclass

`endif
 