`ifndef LFC_RAM_ACTIVE_SQR_SVH
`define LFC_RAM_ACTIVE_SQR_SVH

`include "uvm_macros.svh"
`include "lfc_ram_transaction.svh"

import uvm_pkg::*;

class lfc_ram_active_sqr extends uvm_sequencer#(lfc_ram_transaction);
    `uvm_component_utils(lfc_ram_active_sqr);

    function new(string name = "lfc_ram_active_sqr", uvm_component parent);
        super.new(name, parent);
        `uvm_info("RAM_SQR", "Constructor", UVM_HIGH)
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("RAM_SQR", "Build Phase", UVM_HIGH)
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("RAM_SQR", "Connect Phase", UVM_HIGH)=
    endfunction

endclass

`endif