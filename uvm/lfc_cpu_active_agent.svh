import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_cpu_active_driver.svh"
`include "lfc_cpu_active_monitor.svh"
`include "lfc_cpu_active_sqr.svh"

class lfc_cpu_active_agent extends uvm_agent;
    `uvm_component_utils(lfc_cpu_active_agent)
    lfc_cpu_active_sqr sqr;
    lfc_cpu_active_driver drv;
    lfc_cpu_active_monitor mon;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        sqr = lfc_cpu_active_sqr::type_id::create("sqr", this);
        drv = lfc_cpu_active_driver::type_id::create("drv", this);
        mon = lfc_cpu_active_monitor::type_id::create("mon", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        drv.seq_item_port.connect(sqr.seq_item_export);
    endfunction

endclass