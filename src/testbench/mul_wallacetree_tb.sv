// To run this: verilator --binary -j 0 -Wall -Wno-fatal mul_wallacetree_tb -Imodules -Itestbench -Iinclude --hierarchical --trace; ./obj_dir/Vmul_wallacetree_tb;

`timescale 1ns / 10ps

module mul_wallacetree_tb();
  logic[10:0] tb_a, tb_b;
  logic[22:0] tb_out, golden_out;
  logic tb_clk;
  integer i;
  integer failed_cases;

  parameter SEED = 29;
  parameter NUM_TESTS = 50;

  initial begin
    tb_clk = 0;
    forever
      #1 tb_clk++;
  end

  assign golden_out = tb_a * tb_b;
  mul_wallacetree DUT(.a(tb_a), .b(tb_b), .result(tb_out));

  initial begin
    $dumpfile("waves.vcd");
    $dumpvars();
    tb_a = 11'b10101110101;
    tb_b = 11'b11010111010;

    //Test a bunch of random numbers
    //$timeformat(-9, 2, " ns");
    failed_cases = 0;
    //verilator lint_off WIDTHTRUNC
    for(i = 0; i < NUM_TESTS; i++) begin
      tb_a = $urandom(SEED+i);
      tb_b = $urandom(SEED+i+2);
      //verilator lint_on WIDTHTRUNC
      #2

      if(tb_out != golden_out) begin
        $display("Uh oh, output mismatch for test %0d at %0t. Your output: %0d (%0b) Correct output: %0d (%0b)", i, $time, tb_out, tb_out, golden_out, golden_out);
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
