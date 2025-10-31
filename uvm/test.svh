import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_environment.svh"

class test extends uvm_test;
    `uvm_component_utils(test)

    lfc_environment env;
    virtual lfc_if vif;
    lfc_basic_sequence seq; // TODO: fill out this file

    function new(string name = "test", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    env = lfc_environment::type_id::create("env", this);
    seq = lfc_basic_sequence::type_id::create("seq", this);

        // send interface down
        if(!uvm_config_db#(virtual lfc_if)::get(this, "", "lfc_if", vif)) begin
            `uvm_fatal("Test", "No virtual interface for this test")
        end
    uvm_config_db#(virtual lfc_if)::set(this, "env.cpu_active_ag*", "lfc_if", vif);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting sequence in main phase");
        $display("%t Starting sequence run_phase", $time);
    seq.start(env.cpu_active_ag.sqr);
        #100ns;
        phase.drop_objection(this, "Finished in main phase");
    endtask

endclass`