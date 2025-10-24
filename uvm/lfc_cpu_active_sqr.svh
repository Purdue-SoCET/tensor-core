`ifndef LFC_CPU_ACTIVE_SQR_SVH
`define LFC_CPU_ACTIVE_SQR_SVH

`include "uvm_macros.svh"
`include "lfc_cpu_transaction.svh"

import uvm_pkg::*;

class lfc_cpu_active_sqr extends uvm_sequencer#(lfc_cpu_transaction);
    `uvm_component_utils(lfc_cpu_active_sqr);

    function new(string name = "lfc_cpu_active_sqr", uvm_component parent);
        super.new(name, parent);
        `uvm_info("CPU_SQR", "Constructor", UVM_HIGH)
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("CPU_SQR", "Build Phase", UVM_HIGH)
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("CPU_SQR", "Connect Phase", UVM_HIGH)
    endfunction

endclass

`endif