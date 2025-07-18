import uvm_pkg::*;
`include "uvm_macros.svh"
`include "systolic_if.svh"

class monitor extends uvm_monitor;
  `uvm_component_utils(monitor)

  virtual systolic_if vif;

  uvm_analysis_port#(transaction) systolic_ap;
  uvm_analysis_port#(transaction) result_ap;
  transaction prev_tx; // check if new transaction has been sent

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
    systolic_ap = new("systolic_ap", this);
    result_ap = new("result_ap", this);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual systolic_if)::get(this, "", "systolic_vif", vif)) begin
      `uvm_fatal("Monitor", "No virtual interface specified for this monitor instance")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    prev_tx = transaction#(4)::type_id::create("prev_tx"); // does 4 mean number of input transactions sent for test?
    forever begin
      transaction tx;
  //     @(posedge vif.clk);
  //     tx = transaction#(4)::type_id::create("tx");
  //     tx.a = vif.a;
  //     tx.b = vif.b;
  //     tx.carry_in = vif.carry_in;

  //     if (!tx.input_equal(prev_tx)) begin // if new transaction has been sent
  //       adder_ap.write(tx);
  //       // get outputs from DUT and send to scoreboard/comparator
 // @(posedge vif.clk)
  //       tx.result_sum = vif.sum;
  //       tx.result_overflow = vif.overflow;
  //       result_ap.write(tx);
  //       prev_tx.copy(tx);




  //     end

      @(posedge vif.clk);
  ////input matrix
      for(int i = 0;i < 4; i++) begin
      @(posedge vif.clk);
      input_matrix[i] = vif.array_in;
      end
      @(posedge vif.clk);
      


      ////weight matrix
      for(int i = 0;i < 4; i++) begin // does it elaborate all iterations at once?
      @(posedge vif.clk);
      weight_matrix[i] = vif.array_in;
      end
      @(posedge vif.clk);

      ////partial matrix
      for(int i = 0;i < 4; i++) begin
      @(posedge vif.clk);
      partial_matrix[i] = vif.array_in_partials;
      end
      @(posedge vif.clk);


      
      for(int i = 0;i< 4;i++)begin
      @(posedge vif.out_en);
      out_matrix[i] = vif.array_output;
      end
      @(negedge vif.out_en);
    end
  endtask: run_phase
endclass: monitor
 