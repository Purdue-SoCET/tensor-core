import uvm_pkg::*;
`include "uvm_macros.svh"
`include "transaction.svh"

class systolic_sequence extends uvm_sequence#(transaction);
  `uvm_object_utils(systolic_sequence)

  function new(string name = "");
    super.new(name);
  endfunction: new

  task body();
    
    transaction req_item;
    req_item = transaction#(4)::type_id::create("req_item");
    `uvm_info ("Sequence", $sformatf ("Before Start Item"), UVM_NONE)
    // Pass matrices
    
    repeat(1) begin
      `uvm_info ("Sequence", $sformatf ("Before Start Item"), UVM_NONE)
      start_item(req_item);
      `uvm_info ("Sequence", $sformatf ("After Start Item"), UVM_NONE)
      if(!req_item.randomize()) begin
        `uvm_fatal("Sequence", "Not able to randomize")
      end
      else begin
        `uvm_info ("Sequence", $sformatf ("Randomise Succesful"), UVM_NONE)
  
      end
      finish_item(req_item);
      `uvm_info ("Sequence", $sformatf ("Randomise Succesful"), UVM_NONE)
    end

  
    // // repeat randomized test cases
    // repeat(25) begin
    //   start_item(req_item);
    //   if(!req_item.randomize()) begin
    //     `uvm_fatal("Sequence", "Not able to randomize")
    //   end
    //   finish_item(req_item);
    // end
  endtask: body
endclass


