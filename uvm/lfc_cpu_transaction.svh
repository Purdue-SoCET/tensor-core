`ifndef LFC_CPU_TRANSACTION_SVH
`define LFC_CPU_TRANSACTION_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"

class lfc_cpu_transaction #(parameter NUM_BANKS = 4, parameter UUID_SIZE = 4) extends uvm_sequence_item;
  
  // Reset Input
  logic n_rst;

  // CPU Inputs
  logic mem_in;
  rand logic [31:0] mem_in_addr;
  logic mem_in_rw_mode;
  rand logic [31:0] mem_in_store_value;
  logic dp_in_halt;

  // CPU Outputs
  logic [3:0] mem_out_uuid;
  logic stall;
  logic hit;
  logic [31:0] hit_load;
  logic [NUM_BANKS-1:0] block_status;
  logic [NUM_BANKS-1:0][UUID_SIZE-1:0] uuid_block;
  logic dp_out_flushed;

  `uvm_object_utils_begin(lfc_cpu_transaction) // change some of these to uvm_field_array_int
    `uvm_field_int(n_rst, UVM_DEFAULT)
    `uvm_field_int(mem_in, UVM_DEFAULT)
    `uvm_field_array_int(mem_in_addr, UVM_DEFAULT)
    `uvm_field_int(mem_in_rw_mode, UVM_DEFAULT)
    `uvm_field_array_int(mem_in_store_value, UVM_DEFAULT)
    `uvm_field_int(dp_in_halt, UVM_DEFAULT)
    `uvm_field_array_int(mem_out_uuid, UVM_DEFAULT)
    `uvm_field_int(stall, UVM_DEFAULT)
    `uvm_field_int(hit, UVM_DEFAULT)
    `uvm_field_array_int(hit_load, UVM_DEFAULT)
    `uvm_field_array_int(block_status, UVM_DEFAULT)
    `uvm_field_array_int(uuid_block, UVM_DEFAULT)
    `uvm_field_int(dp_out_flushed, UVM_DEFAULT)
  `uvm_object_utils_end

  // add constraints for randomization

  function new(string name = "lfc_cpu_transaction");
    super.new(name);
  endfunction: new

endclass

`endif
