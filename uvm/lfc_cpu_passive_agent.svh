import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_cpu_passive_monitor.svh"

class lfc_cpu_passive_agent extends uvm_agent;
    `uvm_component_utils(lfc_cpu_passive_agent)
    lfc_cpu_passive_monitor mon;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        mon = lfc_cpu_passive_monitor::type_id::create("mon", this);
    endfunction

endclass