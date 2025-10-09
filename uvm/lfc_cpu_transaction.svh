`ifndef LFC_CPU_TRANSACTION_SVH
`define LFC_CPU_TRANSACTION_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"

class lfc_cpu_transaction #(parameter NUM_BANKS = 4, parameter UUID_SIZE = 4) extends uvm_sequence_item;
  
  // CPU Inputs
  logic n_rst;
  logic mem_in;
  rand logic [31:0] mem_in_addr;
  logic mem_in_rw_mode; // 0 = read, 1 = write
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

  `uvm_object_utils_begin(lfc_cpu_transaction)
    `uvm_field_int(mem_out_uuid, UVM_DEFAULT)
    `uvm_field_int(stall, UVM_DEFAULT)
    `uvm_field_int(hit, UVM_DEFAULT)
    `uvm_field_int(hit_load, UVM_DEFAULT)
    `uvm_field_int(block_status, UVM_DEFAULT)
    `uvm_field_int(uuid_block, UVM_DEFAULT)
    `uvm_field_int(dp_out_flushed, UVM_DEFAULT)
  `uvm_object_utils_end

  // add constraints for randomization

  function new(string name = "lfc_cpu_transaction");
    super.new(name);
  endfunction: new

endclass

`endif
