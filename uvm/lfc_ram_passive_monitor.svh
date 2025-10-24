// lfc_ram_passive_monitor.svh
`ifndef LFC_RAM_PASSIVE_MONITOR_SVH
`define LFC_RAM_PASSIVE_MONITOR_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_if.svh"

// --- Replace these with your real types if needed ---
typedef virtual lfc_if lfc_ram_vif_t;   // TODO: interface
//typedef lfc_cpu_item       cpu_txn_t;       // TODO: sequence_item

class lfc_ram_passive_monitor extends uvm_monitor;
  `uvm_component_utils(lfc_ram_passive_monitor)

  // analysis port to scoreboard/subscribers
  //uvm_analysis_port #(cpu_txn_t) ap;

  // optional: virtual interface handle
  lfc_ram_vif_t vif;

  uvm_analysis_port#(lfc_ram_transaction) result_ap;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
    result_ap = new("result", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //ap = new("ap", this);
    // optional: get VIF from config_db
    if(!uvm_config_db#(virtual lfc_if)::get(this, "", "lfc_vif", vif)) begin
      `uvm_fatal("Monitor", "No virtual interface specified for this monitor instance")
    end
  endfunction

  // minimal placeholder; add your sampling here
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
        // TODO: fill this sucker in
    end
  endtask

endclass

`endif // LFC_CPU_ACTIVE_MONITOR_SVH
