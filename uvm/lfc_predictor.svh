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

    uvm_tlm_analysis_fifo#(lfc_cpu_transaction) expected_MSHR;
    int MSHR_occupancy = 0;
    

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        pred_cpu_ap = new("pred_cpu_ap", this);
        pred_ram_ap = new("pred_ram_ap", this);
    endfunction: build_phase

    function void write(lfc_cpu_transaction cpu_t, lfc_ram_transaction ram_t);
        output_cpu_tx = lfc_cpu_transaction#(NUM_BANKS, UUID_SIZE);
        output_ram_tx = lfc_ram_transaction#(NUM_BANKS);
        output_cpu_tx.copy(cpu_t);
        output_ram_tx.copy(ram_t);

        // TODO: calculate expected outputs below

        if (!cpu_t.hit) begin // cache miss
            MSHR_occupancy++;

            // add transaction to a fifo
            // expected_MSHR.push(cpu_t)
        end 

        if (ram_t.ram_mem_complete) begin // a cache miss is being serviced
            MSHR_occupancy--;

            // remove transaction from fifo corresponding to ram_t.ram_mem_addr
            // expected_MSHR.pop[ram_t.ram_mem_addr];
        end

        if MSHR_occupancy > 8 begin // overflow of MSHR buffer
            output_cpu.stall = 1;
        end else begin
            output_cpu.stall = 0;
        end

        pred_cpu_ap.write(output_cpu_tx);
        pred_ram_ap.write(output_ram_tx);
    endfunction: write


endclass: predictor