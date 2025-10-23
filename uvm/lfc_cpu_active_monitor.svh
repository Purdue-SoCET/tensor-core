// lfc_cpu_active_monitor.svh
`ifndef LFC_CPU_ACTIVE_MONITOR_SVH
`define LFC_CPU_ACTIVE_MONITOR_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"

// --- Replace these with your real types if needed ---
typedef virtual lfc_cpu_if lfc_cpu_vif_t;   // TODO: interface
typedef lfc_cpu_item       cpu_txn_t;       // TODO: sequence_item

class lfc_cpu_active_monitor extends uvm_monitor;
  `uvm_component_utils(lfc_cpu_active_monitor)

  // analysis port to scoreboard/subscribers
  uvm_analysis_port #(cpu_txn_t) ap;

  // optional: virtual interface handle
  lfc_cpu_vif_t vif;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    // optional: get VIF from config_db
    void'(uvm_config_db#(lfc_cpu_vif_t)::get(this, "", "vif", vif));
  endfunction

  // minimal placeholder; add your sampling here
  virtual task run_phase(uvm_phase phase);
    forever begin
      // TODO: sample at @(posedge vif.clk); create cpu_txn_t t; ap.write(t);
      @(posedge $urandom); // placeholder to avoid zero-delay loop
    end
  endtask

endclass

`endif // LFC_CPU_ACTIVE_MONITOR_SVH
