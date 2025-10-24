import uvm_pkg::*;
`include "uvm_macros.svh"

class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(scoreboard)

    uvm_analysis_export#(lfc_cpu_transaction) expected_cpu_export;
    uvm_analysis_export#(lfc_cpu_transaction) actual_cpu_export;
    uvm_analysis_export#(lfc_ram_transaction) expected_ram_export;
    uvm_analysis_export#(lfc_ram_transaction) actual_ram_export;
    uvm_tlm_analysis_fifo#(transaction) expected_cpu_fifo;
    uvm_tlm_analysis_fifo#(transaction) actual_cpu_fifo;
    uvm_tlm_analysis_fifo#(transaction) expected_ram_fifo;
    uvm_tlm_analysis_fifo#(transaction) actual_ram_fifo;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        expected_cpu_export = new("expected_cpu_export", this);
        actual_cpu_export = new("actual_cpu_export", this);
        expected_ram_export = new("expected_ram_export", this);
        actual_ram_export = new("actual_ram_export", this);
        expected_cpu_fifo = new("expected_cpu_fifo", this);
        actual_cpu_fifo = new("actual_cpu_fifo", this);
        expected_ram_fifo = new("expected_ram_fifo", this);
        actual_ram_fifo = new("actual_ram_fifo", this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        expected_cpu_export.connect(expected_cpu_fifo.analysis_export);
        actual_cpu_export.connect(actual_cpu_fifo.analysis_export);
        expected_ram_export.connect(expected_ram_fifo.analysis_export);
        actual_ram_export.connect(actual_ram_fifo.analysis_export);
    endfunction

    task run_phase(uvm_phase phase);
        // TODO: make the run_phase
    endtask: run_phase

    function void report_phase(uvm_phase phase);
        // TODO: figure out what to report
        uvm_report_info();
        uvm_report_info();
    endfunction: report_phase

endclass