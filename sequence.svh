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
    
    // should repeat(4) be added with a randomize?
    // Pass matrices
    start_item(req_item);
    req_item.input_matrix = '{
      '{16'h0001, 16'h0002, 16'h0003, 16'h0004},
      '{16'h0005, 16'h0006, 16'h0007, 16'h0008},
      '{16'h0009, 16'h000A, 16'h000B, 16'h000C},
      '{16'h000D, 16'h000E, 16'h000F, 16'h0010}
    };

    req_item.weight_matrix = '{
      '{16'h0001, 16'h0002, 16'h0003, 16'h0004},
      '{16'h0005, 16'h0006, 16'h0007, 16'h0008},
      '{16'h0009, 16'h000A, 16'h000B, 16'h000C},
      '{16'h000D, 16'h000E, 16'h000F, 16'h0010}
    };

    req_item.partial_matrix = '{
      '{16'h0001, 16'h0002, 16'h0003, 16'h0004},
      '{16'h0005, 16'h0006, 16'h0007, 16'h0008},
      '{16'h0009, 16'h000A, 16'h000B, 16'h000C},
      '{16'h000D, 16'h000E, 16'h000F, 16'h0010}
    };

    finish_item(req_item);

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


