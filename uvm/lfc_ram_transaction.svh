`ifndef LFC_RAM_TRANSACTION_SVH
`define LFC_RAM_TRANSACTION_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"

class lfc_ram_transaction #(parameter NUM_BANKS = 4) extends uvm_sequence_item;
    rand bit [NUM-1:0][31:0] ram_mem_data;

    `uvm_object_utils_begin(lfc_ram_transaction)
        `uvm_field

endclass

`endif