`include "isa_types.vh"
`include "vdiv_if.vh"
`timescale 1 ns / 1 ns

module vdiv_tb;
  string tb_test_case = "INIT";
  logic CLK = 0;
  logic nRST = 0;
  parameter PERIOD = 10;
  
  // Testbench signals
  reg [15:0] a, b, expected_result;
  integer errors;
  integer normal_tests, subnormal_input_tests, subnormal_output_tests, edge_tests;
  
  // File I/O
  integer fd;
  integer r;
  
  always #(PERIOD/2) CLK++;
  
  vdiv_if divif();
  vdiv DUT(.CLK(CLK), .nRST(nRST), .divif(divif));
  
  // Helper function to check if fp16 value is NaN
  function automatic bit is_fp16_nan(input logic [15:0] val);
    logic [4:0] exponent = val[14:10];
    logic [9:0] mantissa = val[9:0];
    return (exponent == 5'b11111) && (mantissa != 10'b0);
  endfunction
  
  // Task to apply test vector
  task apply_vector(
    input [15:0] a_in,
    input [15:0] b_in,
    input [15:0] expected_in
  );
  begin
    @(posedge CLK);
    divif.a = a_in;
    divif.b = b_in;
    divif.en = 1;
    expected_result = expected_in;
    
    @(posedge CLK);
    wait (divif.done == 1);
    divif.en = 0;
    
    // Check for NaN condition before direct comparison
    if (is_fp16_nan(divif.result) && is_fp16_nan(expected_in)) begin
      // Both are NaNs, consider it a match
    end else if (divif.result !== expected_in) begin
      $display("ERROR @%0t [%s]: %h / %h = %h (expected %h)", 
               $time, tb_test_case, divif.a, divif.b, divif.result, expected_in);
      errors = errors + 1;
    end
    @(posedge CLK);
  end
  endtask
  
  // Task to run file-based tests
  task run_file_tests(input string filename, input string test_name);
    integer test_count;  // Declare without initialization
  begin
    test_count = 0;      // Initialize inside begin-end block
    tb_test_case = test_name;
    
    fd = $fopen(filename, "r");
    if (fd == 0) begin
      $display("ERROR: Cannot open file: %s", filename);
      $stop;
    end
    
    $display("Running %s from %s...", test_name, filename);
    
    while (!$feof(fd)) begin
      r = $fscanf(fd, "%h,%h,%h\n", a, b, expected_result);
      if (r == 3) begin
        apply_vector(a, b, expected_result);
        test_count++;
      end
    end
    
    $fclose(fd);
    $display("Completed %s: %0d tests run", test_name, test_count);
  end
  endtask
  
  // Task to run explicit edge case tests
  task run_edge_case_tests();
    // FP16 constants - MUST be declared at the top
    localparam [15:0] POS_ZERO     = 16'h0000;
    localparam [15:0] NEG_ZERO     = 16'h8000;
    localparam [15:0] POS_INF      = 16'h7C00;
    localparam [15:0] NEG_INF      = 16'hFC00;
    localparam [15:0] POS_ONE      = 16'h3C00;
    localparam [15:0] NEG_ONE      = 16'hBC00;
    localparam [15:0] POS_TWO      = 16'h4000;
    localparam [15:0] NEG_TWO      = 16'hC000;
    localparam [15:0] QNAN         = 16'h7E00;  // Quiet NaN
    localparam [15:0] SNAN         = 16'h7D00;  // Signaling NaN
    localparam [15:0] POS_MIN_NORM = 16'h0400;  // Smallest positive normal
    localparam [15:0] NEG_MIN_NORM = 16'h8400;  // Smallest negative normal
    localparam [15:0] POS_MAX_NORM = 16'h7BFF;  // Largest positive normal
    localparam [15:0] NEG_MAX_NORM = 16'hFBFF;  // Largest negative normal
    localparam [15:0] POS_MIN_SUB  = 16'h0001;  // Smallest positive subnormal
    localparam [15:0] NEG_MIN_SUB  = 16'h8001;  // Smallest negative subnormal
    localparam [15:0] POS_MAX_SUB  = 16'h03FF;  // Largest positive subnormal
    localparam [15:0] NEG_MAX_SUB  = 16'h83FF;  // Largest negative subnormal
  begin
    tb_test_case = "EDGE_CASES";
    $display("Running explicit FP16 edge case tests...");
    
    // Division by zero
    tb_test_case = "ZERO_CASES";
    apply_vector(POS_ONE, POS_ZERO, POS_INF);     // 1 / 0 = inf
    apply_vector(POS_ZERO, POS_ONE, POS_ZERO);    // 0 / 1 = 0
    apply_vector(POS_ZERO, POS_ZERO, QNAN);       // 0 / 0 = NaN
    
    // Infinity cases
    tb_test_case = "INF_CASES";
    apply_vector(POS_INF, POS_ONE, POS_INF);      // inf / 1 = inf
    apply_vector(POS_ONE, POS_INF, POS_ZERO);     // 1 / inf = 0
    apply_vector(POS_INF, POS_ZERO, POS_INF);     // inf / 0 = inf
    apply_vector(POS_ZERO, POS_INF, POS_ZERO);    // 0 / inf = +0
    apply_vector(POS_INF, POS_INF, QNAN);         // inf / inf = NaN
    
    // NaN propagation
    tb_test_case = "NAN_PROPAGATION";
    apply_vector(QNAN, POS_ONE, QNAN);            // NaN / 1 = NaN
    apply_vector(POS_ONE, QNAN, QNAN);            // 1 / NaN = NaN
    apply_vector(QNAN, QNAN, QNAN);               // NaN / NaN = NaN
    apply_vector(SNAN, POS_ONE, QNAN);            // sNaN / 1 = qNaN
    apply_vector(QNAN, POS_INF, QNAN);            // NaN / inf = NaN
    apply_vector(POS_INF, QNAN, QNAN);            // inf / NaN = NaN
    apply_vector(QNAN, POS_ZERO, QNAN);           // NaN / 0 = NaN
    apply_vector(POS_ZERO, QNAN, QNAN);           // 0 / NaN = NaN
    
    // Boundary normal numbers
    tb_test_case = "NORM_BOUNDARY";
    apply_vector(POS_MAX_NORM, POS_ONE, POS_MAX_NORM);  // max / 1 = max
    apply_vector(POS_MIN_NORM, POS_ONE, POS_MIN_NORM);  // min / 1 = min
    apply_vector(POS_MAX_NORM, POS_MAX_NORM, POS_ONE);  // max / max = 1
    apply_vector(POS_MIN_NORM, POS_MIN_NORM, POS_ONE);  // min / min = 1

    // Subnormal boundary cases
    tb_test_case = "SUBNORM_BOUNDARY";
    apply_vector(POS_MIN_SUB, POS_ONE, POS_ZERO);       // min_sub / 1: DTZ treats input as 0, result = 0
    apply_vector(POS_MAX_SUB, POS_ONE, POS_ZERO);       // max_sub / 1: DTZ treats input as 0, result = 0
    apply_vector(POS_MIN_SUB, POS_TWO, POS_ZERO);       // min_sub / 2: DTZ treats input as 0, result = 0
    apply_vector(POS_ONE, POS_MAX_NORM, 16'h0100);      // 1 / max_norm: result is small subnormal, not flushed
    
    // Overflow cases
    tb_test_case = "OVERFLOW";
    apply_vector(POS_MAX_NORM, POS_MIN_SUB, POS_INF);   // max / min_sub = +inf (overflow)
    apply_vector(NEG_MAX_NORM, POS_MIN_SUB, NEG_INF);   // -max / min_sub = -inf
    
    $display("Edge case tests completed");
    edge_tests = errors - normal_tests - subnormal_input_tests - subnormal_output_tests;
  end
  endtask
  
  initial begin
    divif.en = 0;
    divif.a = 0;
    divif.b = 0;
    errors = 0;
    normal_tests = 0;
    subnormal_input_tests = 0;
    subnormal_output_tests = 0;
    edge_tests = 0;

    // Power-on reset test
    tb_test_case = "POWER_ON_RESET";
    $display("Running power-on reset test...");
    
    @(posedge CLK);
    if (divif.done !== 0) begin
      $display("ERROR @%0t [POWER_ON_RESET]: done should be 0 during reset, got %b", $time, divif.done);
      errors = errors + 1;
    end else begin
      $display("Power-on reset test passed");
    end
    
    #20 nRST = 1;
    #20;  // Allow some settling time
    
    // Run normal number tests
    run_file_tests("testcases/vdiv_normal_tests_10K.csv", "NORMAL_TESTS");
    normal_tests = errors;
    
    // Run subnormal number input tests
    run_file_tests("testcases/vdiv_subnormal_input_tests_10K.csv", "SUBNORMAL_INPUT_TESTS");
    subnormal_input_tests = errors - normal_tests;

    // Run subnormal number output tests
    run_file_tests("testcases/vdiv_subnormal_output_tests_10K.csv", "SUBNORMAL_OUTPUT_TESTS");
    subnormal_output_tests = errors - normal_tests;
    
    // Run explicit edge case tests
    run_edge_case_tests();
    edge_tests = errors - normal_tests - subnormal_input_tests - subnormal_output_tests;
    
    // Summary
    $display("\n========== TEST SUMMARY ==========");
    $display("Normal tests errors:     %0d", normal_tests);
    $display("Subnormal input tests errors:  %0d", subnormal_input_tests);
    $display("Subnormal output tests errors:  %0d", subnormal_output_tests);
    $display("Edge case tests errors:  %0d", edge_tests);
    $display("Total errors:            %0d", errors);
    $display("==================================\n");
    
    if (errors == 0) 
      $display("*** ALL TESTS PASSED ***");
    else 
      $display("*** TEST FAILED: %0d total errors ***", errors);
    
    $stop;
  end
endmodule