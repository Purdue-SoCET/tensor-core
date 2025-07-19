import uvm_pkg::*;
`include "uvm_macros.svh"
`include "agent.svh"
`include "systolic_array_if.vh"
`include "comparator.svh"
`include "predictor.svh"
`include "transaction.svh"

class environment extends uvm_env;
  `uvm_component_utils(environment)

  agent agt;
  predictor pred;
  comparator comp;

  function new(string name = "env", uvm_component parent = null);
		super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    agt = agent::type_id::create("agt", this);
    pred = predictor::type_id::create("pred", this);
    comp = comparator::type_id::create("comp", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    agt.mon.systolic_ap.connect(pred.analysis_export); // connect monitor to predictor
    pred.pred_ap.connect(comp.expected_export); // connect predictor to comparator
    agt.mon.result_ap.connect(comp.actual_export); // connect monitor to comparator
  endfunction

endclass: environment
