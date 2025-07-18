import uvm_pkg::*;
`include "uvm_macros.svh"
`include "sys_if.svh"

class driver extends uvm_driver#(transaction);
  `uvm_component_utils(driver)

  virtual sys_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction: new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get interface
    if(!uvm_config_db#(virtual sys_if)::get(this, "", "sys_vif", vif)) begin
      `uvm_fatal("Driver", "No virtual interface specified for this test instance");
    end
  endfunction: build_phase

  task run_phase(uvm_phase phase);
    transaction req_item;
    vif.check = 0;

    forever begin
      seq_item_port.get_next_item(req_item);
      // DUT_reset();
      // vif.a = req_item.a;
      // vif.b = req_item.b;
      // vif.carry_in = req_item.carry_in;
      // #(0.2)
      // @(posedge vif.clk);

      ////input matrix
      for(int i = 0;i < 4; i++) begin
      @(posedge vif.clk);
      vif.input_en <= 1;
      vif.array_in <= input_matrix[i] // locally declared, should we get from req_item?
      
      end
      @(posedge vif.clk);
      vif.input_en <= 0;


      ////weight matrix
      for(int i = 0;i < 4; i++) begin
      @(posedge vif.clk);
      vif.weight_en <= 1;
      vif.array_in <= weight_matrix[i]
      
      end
      @(posedge vif.clk);
      vif.weight_en <= 0;

      ////partial matrix
      for(int i = 0;i < 4; i++) begin
      @(posedge vif.clk);
      vif.partial_en <= 1;
      vif.array_in_partials <= partial_matrix[i]
      
      end
      @(posedge vif.clk);
      vif.partial_en <= 0;

      
      repeat(4)@(negedge vif.out_en);




      
      
      seq_item_port.item_done();
    end
  endtask: run_phase

  // task DUT_reset();
  //   @(posedge vif.clk);
  //   vif.n_rst = 1;
  //   @(posedge vif.clk);
  // endtask

endclass: driver
 