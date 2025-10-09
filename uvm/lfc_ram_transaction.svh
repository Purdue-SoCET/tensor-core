`ifndef LFC_RAM_TRANSACTION_SVH
`define LFC_RAM_TRANSACTION_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"

class lfc_ram_transaction #(parameter NUM_BANKS = 4) extends uvm_sequence_item;
    logic n_rst;
    rand logic [NUM_BANKS-1:0][31:0] ram_mem_data;
    logic [NUM_BANKS-1:0] ram_mem_complete;

    logic [NUM_BANKS-1:0] ram_mem_REN;
    logic [NUM_BANKS-1:0] ram_mem_WEN;
    logic [NUM_BANKS-1:0][31:0] ram_mem_addr;
    logic [NUM_BANKS-1:0][31:0] ram_mem_store;


    `uvm_object_utils_begin(lfc_ram_transaction)
        `uvm_field_int(ram_mem_data, UVM_DEFAULT);
        `uvm_field_int(ram_mem_complete, UVM_DEFAULT);
        `uvm_field_int(ram_mem_REN, UVM_DEFAULT);
        `uvm_field_int(ram_mem_WEN, UVM_DEFAULT);
        `uvm_field_int(ram_mem_addr, UVM_DEFAULT);
        `uvm_field_int(ram_mem_store, UVM_DEFAULT);
    `uvm_object_utils_end

    // no current randomization constraints

    function new(string name = "lfc_ram_transaction");
        super.new(name);
    endfunction

endclass

`endif