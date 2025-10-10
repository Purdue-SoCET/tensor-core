`include "vector_if.vh"
`include "vector_types.vh"

`timescale 1 ns / 1 ns

module masku_tb;
  import vector_pkg::*;

  // DUT interface and instance
  vector_if vif();
  masku     dut(.vif(vif));   // masku (vector_if.masku vif)

  initial begin
    string testname;
    $display("testing masku...");

    testname = "Low VM";
    vif.masku_in.vm    = 1'b0;
    vif.masku_in.vmask = '0;      // ignored when vm=0
    #10;

    testname = "High VM";
    vif.masku_in.vm    = 1'b1;
    vif.masku_in.vmask = {NUM_LANES{2'b01}};
    #10;

    $stop;
  end
endmodule
