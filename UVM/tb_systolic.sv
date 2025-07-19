import uvm_pkg::*;
`include "systolic_array.sv"
`include "systolic_array_if.vh"
`include "test.svh"

module tb_systolic();
  logic clk, tb_nRST;

  // generate clock
  initial begin
    clk = 0;
    forever #10 clk = !clk;
  end

  systolic_array_if systolic_if(clk);

    task reset;
        begin
        tb_nRST = 1'b0;
        @(posedge clk);
        @(posedge clk);
        @(negedge clk);
        tb_nRST = 1'b1;
        @(posedge clk);
        @(posedge clk);
        end
    endtask
    
  systolic_array systolic(clk, tb_nRST, systolic_if.memory_array);
  initial begin
    uvm_config_db#(virtual systolic_array_if)::set(null, "", "systolic_vif", systolic_if);
    // reset();
    run_test("test");
  end

endmodule
