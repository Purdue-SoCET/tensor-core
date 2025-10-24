import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_cpu_transaction.svh"
`include "lfc_ram_transaction.svh"

class lfc_predictor extends uvm_subscriber#(lfc_cpu_transaction, lfc_ram_transaction);
    `uvm_component_utils(lfc_predictor)

    uvm_analysis_port#(lfc_cpu_transaction) pred_cpu_ap;
    uvm_analysis_port#(lfc_ram_transaction) pred_ram_ap;

    lfc_cpu_transaction output_cpu_tx;
    lfc_ram_transaction output_ram_tx;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        pred_cpu_ap = new("pred_cpu_ap", this);
        pred_ram_ap = new("pred_ram_ap", this);
    endfunction: build_phase

    function void write(lfc_cpu_transaction cpu_t, lfc_ram_transaction ram_t);
        output_cpu_tx = lfc_cpu_transaction#(___, ___);
        output_ram_tx = lfc_ram_transaction#(___);
        output_cpu_tx.copy(cpu_t);
        output_ram_tx.copy(ram_t);

        // TODO: calculate expected outputs here


        pred_cpu_ap.write(output_cpu_tx);
        pred_ram_ap.write(output_ram_tx);
    endfunction: write


endclass: predictor