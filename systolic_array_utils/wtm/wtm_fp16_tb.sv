`timescale 1ns/1ps
`default_nettype none

module wtm_fp16_tb;

  // DUT ports
  logic [15:0] A, B;
  logic [15:0] S;
  logic [1:0]  E;

  // Instantiate DUT
  wtm_fp16 dut (
    .A(A),
    .B(B),
    .S(S),
    .E(E)
  );

  // Task for applying stimulus
  task run_test(input [15:0] a, input [15:0] b, string name);
    begin
      A = a;
      B = b;
      #5; // wait for propagation
      $display("[%s] A=0x%h, B=0x%h -> S=0x%h, E=%0d", name, A, B, S, E);
    end
  endtask

  initial begin
    $dumpfile("waves/wtm_fp16.vcd"); 
    $dumpvars(0, wtm_fp16_tb); 
    $display("=== Wallace Tree FP16 Multiplier Testbench ===");

    // Basic cases
    run_test(16'h0000, 16'h3C00, "Zero * 1.0");
    run_test(16'h3C00, 16'h3C00, "1.0 * 1.0");
    run_test(16'h4000, 16'h4000, "2.0 * 2.0");
    run_test(16'hC000, 16'h4000, "-2.0 * 2.0");

    // Edge cases
    run_test(16'h7C00, 16'h3C00, "Inf * 1.0");
    run_test(16'h7C00, 16'h7C00, "Inf * Inf");
    run_test(16'h7E00, 16'h3C00, "NaN * 1.0");
    run_test(16'h7E00, 16'h7E00, "NaN * NaN");
    run_test(16'h0001, 16'h3C00, "Denormal * 1.0");

    $display("=== Testbench complete ===");
    $finish;
  end
  // 3C00 is 1.0 in FP16 (sign=0, exp=15, frac=0).
  // 4000 is 2.0 in FP16.
  // 7C00 is +Infinity.
  // 7E00 is NaN.
  // 0000 is +0.
  // 0001 is a denormalized tiny number.
endmodule
