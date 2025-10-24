import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_if.svh"

class lfc_cpu_active_driver extends uvm_driver#(lfc_cpu_transaction);
    `uvm_component_utils(lfc_cpu_active_driver)

    virtual lfc_if vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual lfc_if)::get(this, "", "lfc_vif", vif)) begin
            `uvm_fatal("Driver", "No virtual interface specified for this test instance");
        end
    endfunction

    task DUT_reset();
        @(posedge vif.clk);
        vif.n_rst = 0;
        @(posedge vif.clk);
        vif.n_rst = 1;
        @(posedge vif.clk);
    endtask

    task run_phase(uvm_phase phase);
        lfc_cpu_transaction req_item;

        forever begin
            seq_item_port.get_next_item(req_item);
            DUT_reset(); // 3 clock cycles
            vif.mem_in = req_item.mem_in; // not random
            vif.mem_in_addr = req_item.mem_in_addr;
            vif.mem_in_rw_mode = req_item.mem_in_rw_mode; // not random
            vif.mem_in_store_value = req_item.mem_in_store_value;
            vif.dp_in_halt = req_item.dp_in_halt; // not random
            #(.2);
            @(posedge vif.clk);
            seq_item_port.item_done();
        end
    endtask

endclass