// Malcolm McClymont's 8 bit wallace tree from ECE 559
// re-used here to test 8 bit wallace tree for BF16 multiplier.

// to run this: verilator --binary -j 0 -Wall -Wno-fatal wallacetree_8b_tb -Imodules -Itestbench -Iinclude --hierarchical --trace; ./obj_dir/Vwallacetree_8b_tb; gtkwave waves/wallacetree_8b_waves.vcd --save=waves/wallacetree_8b_debug.gtkw

/* verilator lint_off UNUSEDSIGNAL */
`timescale 1ns / 10ps

module wallacetree_8b_tb();
  logic[7:0] tb_a, tb_b;
  logic[9:0] tb_out;
  logic[15:0] tb_debug_output;
  logic[15:0] golden_out;
  logic tb_clk;
  integer i;
  integer failed_cases;

  logic tb_ovf, tb_roundloss;

  parameter SEED = 10;
  parameter NUM_TESTS = 20;

  initial begin
    tb_clk = 0;
    forever
      #1 tb_clk++;
  end

  assign golden_out = tb_a * tb_b;
  wallacetree_8b trash_heap (.a(tb_a), .b(tb_b), .result(tb_out), .overflow(tb_ovf), .round_loss(tb_roundloss), .debug_output(tb_debug_output));

  initial begin
    $dumpfile("waves/wallacetree_8b_waves.vcd");
    $dumpvars();
    tb_a = 8'b01011101;
    tb_b = 8'b10101110;

    //Test a bunch of random numbers
    //$timeformat(-9, 2, " ns");
    failed_cases = 0;
    //verilator lint_off WIDTHTRUNC
    for(i = 0; i < NUM_TESTS; i++) begin
      tb_a = $urandom(SEED+i);
      tb_b = $urandom(SEED+i+2);
      //verilator lint_on WIDTHTRUNC
      #1
      if(tb_debug_output != golden_out) begin
        $display("Uh oh, output mismatch for test %0d at %0t. Your output: %0d (%0b) Correct output: %0d (%0b)", i, $time, tb_debug_output, tb_debug_output, golden_out, golden_out);
        failed_cases += 1;
      end
      #1;  
    end

    if(failed_cases == 0)
      $display("\nAll tests passed!\n");
    else
      $display("\n%0d cases failed, that's rough buddy.\n", i);

    #20;

    $finish();
  end

endmodule
