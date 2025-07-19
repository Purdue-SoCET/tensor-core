import uvm_pkg::*;
`include "uvm_macros.svh"
`include "environment.svh"
`include "sequence.svh"

class test extends uvm_test;
  `uvm_component_utils(test)

  environment env;
  virtual systolic_array_if vif;
  systolic_sequence seq;
  // bit [7:0] exp_data[4] = {8'hBA, 8'h5E, 8'hBA, 8'h11};

  function new(string name = "test", uvm_component parent);
    super.new(name, parent);
  endfunction: new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = environment::type_id::create("env", this);
    seq = systolic_sequence::type_id::create("seq");

    // send interface down
    if (!uvm_config_db#(virtual systolic_array_if)::get(this, "", "systolic_vif", vif)) begin
      `uvm_fatal("Test", "No virtual interface specified for this test instance")
    end

    uvm_config_db#(virtual systolic_array_if)::set(this, "env.agt*", "systolic_vif", vif);
  endfunction: build_phase

//   function void tc_direct_urx_utx::start_of_simulation_phase(uvm_phase phase);

//    foreach (exp_data[i]) begin
//       uart_seqit exp_data_h;
//       exp_data_h = uart_seqit::type_id::create("exp_data_h");
//       exp_data_h.mon_data = exp_data[i];
//       env_h.uart_scoreboard_h.expected_data.push_back(exp_data_h);
//   end

// endfunction:start_of_simulation_phase

  task run_phase(uvm_phase phase);
    phase.raise_objection(this, "Starting sequence in main phase");
    $display("%t Starting sequence run_phase", $time);
    seq.start(env.agt.sqr);
    #100ns;
    `uvm_info("test", "end run_phase", UVM_LOW)
    phase.drop_objection(this, "Finished in main phase");
  endtask
endclass: test
