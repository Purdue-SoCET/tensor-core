// lfc_cpu_active_monitor.svh
`ifndef LFC_CPU_ACTIVE_MONITOR_SVH
`define LFC_CPU_ACTIVE_MONITOR_SVH

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "lfc_if.svh"

// --- Replace these with your real types if needed ---
typedef virtual lfc_if lfc_cpu_vif_t;   // TODO: interface
//typedef lfc_cpu_item       cpu_txn_t;       // TODO: sequence_item

class lfc_cpu_active_monitor extends uvm_monitor;
  `uvm_component_utils(lfc_cpu_active_monitor)

  // analysis port to scoreboard/subscribers
  //uvm_analysis_port #(lfc_cpu_transaction) lfc_ap;

  // optional: virtual interface handle
  lfc_cpu_vif_t vif;

  uvm_analysis_port#(lfc_cpu_transaction) lfc_ap;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
    lfc_ap = new("lfc_ap", this);
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
      // TODO: sample at @(posedge vif.clk); create cpu_txn_t t; lfc_ap.write(t);
      //@(posedge $urandom); // placeholder to avoid zero-delay loop
      lfc_cpu_transaction tx;
      repeat(4) @(posedge vif.clk); // 4 clock edges before input is sent from driver
      tx = transaction::type_id::create("tx");
      tx.mem_in = vif.mem_in;
      tx.mem_in_addr = vif.mem_in_addr;
      tx.mem_in_rw_mode = vif.mem_in_rw_mode;
      tx.mem_in_store_value = vif.mem_in_store_value;
      tx.dp_in_halt = vif.dp_in_halt;
      lfc_ap.write(tx);
    end
  endtask

endclass

`endif // LFC_CPU_ACTIVE_MONITOR_SVH
