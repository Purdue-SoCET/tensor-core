`timescale 1ns/1ns
`include "vector_if.vh"
`include "vector_types.vh"

module masku_wrapper_tb;
  import vector_pkg::*;

  // Instantiate the interface and DUT
  vector_if vif();
  masku_wrapper dut(.vif(vif));

  // Waveform dump (works with many simulators)
  initial begin
    $dumpfile("masku_wrapper_tb.vcd");
    $dumpvars(0, masku_wrapper_tb);
  end

  // Clock and reset
  initial begin
    // Assert reset (active low), start clock low
    vif.nRST = 1'b0;
    vif.CLK  = 1'b0;
    #12;           // hold reset for a couple of ns
    vif.nRST = 1'b1; // release
  end

  // 10ns clock period
  always #5 vif.CLK = ~vif.CLK;

  // Test sequence
  initial begin
    // Wait for reset deassertion (nRST is active-low). When the reset
    // is released there will be a posedge on nRST; wait one clock after
    // that to ensure registers have settled.
    @(posedge vif.nRST);
    @(posedge vif.CLK);
    #1;

    $display("-- TEST 1: VM=0 (expect all zeros)");
    vif.masku_in.vm = 1'b0;
    vif.masku_in.vmask = '0;
    // allow one clock to capture
    @(posedge vif.CLK);
    #1; show_mask();

    $display("\n-- TEST 2: VM=1 replicate pattern {NUM_LANES{2'b01}} ");
    vif.masku_in.vm = 1'b1;
    vif.masku_in.vmask = {NUM_LANES{2'b01}}; // same pattern used in existing tb
    @(posedge vif.CLK);
    #1; show_mask();

    $display("\n-- TEST 3: Per-lane incremental pattern");
    // build a per-lane packed vmask where each lane's SLICE_W bits = lane index
    vif.masku_in.vm = 1'b1;
    vif.masku_in.vmask = '0;
    for (int i = 0; i < NUM_LANES; i++) begin
      vif.masku_in.vmask[i*SLICE_W +: SLICE_W] = i % (1<<SLICE_W);
    end
    @(posedge vif.CLK);
    #1; show_mask();

    $display("\nAll tests done.");
    #5 $stop;
  end

  // Helper task to print the mask per lane
  task show_mask();
    begin
      for (int i = 0; i < NUM_LANES; i++) begin
        $display("lane %0d mask = %b", i, vif.masku_out.mask[i]);
      end
    end
  endtask

endmodule
