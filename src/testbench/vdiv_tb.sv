`include "isa_types.vh"
`include "vdiv_if.vh"
`timescale 1 ns / 1 ns

module vdiv_tb;
  //-----------------------------------------------
  // Configuration Parameters
  //-----------------------------------------------
  // Change these to switch between FP16 and BF16
  parameter int EXP_WIDTH = 8;   // FP16: 5, BF16: 8
  parameter int MANT_WIDTH = 7; // FP16: 10, BF16: 7
  parameter int WIDTH = EXP_WIDTH + MANT_WIDTH + 1;
  
  // Testbench variables
  string tb_test_case = "INIT";
  logic CLK = 0;
  logic nRST = 0;
  parameter PERIOD = 10;
  
  // Testbench tracking variables
  reg [WIDTH-1:0] expected_result;
  integer errors;
  integer normal_tests, subnormal_input_tests, subnormal_output_tests, edge_tests;
  
  // File I/O
  integer fd;
  integer r;

  //-----------------------------------------------
  // Clock generation
  //-----------------------------------------------
  always #(PERIOD/2) CLK = ~CLK;

  //-----------------------------------------------
  // Interface and DUT instantiation
  //-----------------------------------------------
  vdiv_if #(
    .EXP_WIDTH(EXP_WIDTH),
    .MANT_WIDTH(MANT_WIDTH)
  ) divif();

  vdiv DUT (
    .CLK(CLK),
    .nRST(nRST),
    .divif(divif)
  );

  //-----------------------------------------------
  // Helper: check if floating point value is NaN
  //-----------------------------------------------
  function automatic bit is_nan(input logic [WIDTH-1:0] val);
    logic [EXP_WIDTH-1:0] exponent = val[WIDTH-2:MANT_WIDTH];
    logic [MANT_WIDTH-1:0] mantissa = val[MANT_WIDTH-1:0];
    return (exponent == {EXP_WIDTH{1'b1}}) && (mantissa != {MANT_WIDTH{1'b0}});
  endfunction

  //-----------------------------------------------
  // Helper: convert integer to exponent field
  //-----------------------------------------------
  function automatic logic [EXP_WIDTH-1:0] get_exponent(input integer exp_value);
    return exp_value[EXP_WIDTH-1:0];
  endfunction

  //-----------------------------------------------
  // Task: apply test vector with proper handshake
  //-----------------------------------------------
  task automatic apply_vector(
    input [WIDTH-1:0] a_in,
    input [WIDTH-1:0] b_in,
    input [WIDTH-1:0] expected_in
  );
  begin
    // Wait until DUT is ready to accept input
    @(posedge CLK);
    while (!divif.out.ready_in) @(posedge CLK);
    
    // Apply inputs and assert valid_in
    divif.in.operand1 = a_in;
    divif.in.operand2 = b_in;
    divif.in.valid_in = 1;
    expected_result = expected_in;
    
    // Wait for input to be accepted (ready_in goes low)
    @(posedge CLK);
    while (divif.out.ready_in) @(posedge CLK);
    
    // Deassert valid_in after handshake
    divif.in.valid_in = 0;
    
    // Wait for output to be valid
    while (!divif.out.valid_out) @(posedge CLK);
    
    // Assert ready_out to accept the output
    divif.in.ready_out = 1;
    
    // Compare results (special NaN handling)
    if (is_nan(divif.out.result) && is_nan(expected_in)) begin
      // Both NaN — pass
    end else if (divif.out.result !== expected_in) begin
      $display("ERROR @%0t [%s]: %h / %h = %h (expected %h)", 
               $time, tb_test_case, divif.in.operand1, divif.in.operand2, divif.out.result, expected_in);
      errors++;
    end
    
    // Complete the output handshake
    @(posedge CLK);
    divif.in.ready_out = 0;
    
    // Wait for valid_out to deassert
    while (divif.out.valid_out) @(posedge CLK);
  end
  endtask

  //-----------------------------------------------
  // Task: run file-based test set
  //-----------------------------------------------
  task automatic run_file_tests(input string filename, input string test_name);
    integer test_count;
    string format_str;
  begin
    test_count = 0;
    tb_test_case = test_name;
    
    fd = $fopen(filename, "r");
    if (fd == 0) begin
      $display("INFO: Cannot open file: %s (skipping)", filename);
      return;
    end
    
    $display("Running %s from %s...", test_name, filename);
    
    // Construct format string based on WIDTH
    if (WIDTH == 16)
      format_str = "%h,%h,%h\n";
    else
      format_str = "%h,%h,%h\n"; // Same format, parser handles different widths
    
    while (!$feof(fd)) begin
      r = $fscanf(fd, format_str, divif.in.operand1, divif.in.operand2, expected_result);
      if (r == 3) begin
        apply_vector(divif.in.operand1, divif.in.operand2, expected_result);
        test_count++;
      end
    end
    
    $fclose(fd);
    $display("Completed %s: %0d tests run", test_name, test_count);
  end
  endtask

  //-----------------------------------------------
  // Task: run edge case tests
  //-----------------------------------------------
  task automatic run_edge_case_tests();
    // Floating point constants (generated based on parameters)
    logic [WIDTH-1:0] POS_ZERO, NEG_ZERO;
    logic [WIDTH-1:0] POS_INF, NEG_INF;
    logic [WIDTH-1:0] POS_ONE, NEG_ONE;
    logic [WIDTH-1:0] POS_TWO, NEG_TWO;
    logic [WIDTH-1:0] QNAN, SNAN;
    logic [WIDTH-1:0] POS_MIN_NORM, NEG_MIN_NORM;
    logic [WIDTH-1:0] POS_MAX_NORM, NEG_MAX_NORM;
    logic [WIDTH-1:0] POS_MIN_SUB, NEG_MIN_SUB;
    logic [WIDTH-1:0] POS_MAX_SUB, NEG_MAX_SUB;
  begin
    // Initialize constants based on format
    POS_ZERO     = {WIDTH{1'b0}};
    NEG_ZERO     = {1'b1, {(WIDTH-1){1'b0}}};
    POS_INF      = {{1'b0}, {EXP_WIDTH{1'b1}}, {MANT_WIDTH{1'b0}}};
    NEG_INF      = {{1'b1}, {EXP_WIDTH{1'b1}}, {MANT_WIDTH{1'b0}}};
    QNAN         = {{1'b0}, {EXP_WIDTH{1'b1}}, 1'b1, {(MANT_WIDTH-1){1'b0}}};
    SNAN         = {{1'b0}, {EXP_WIDTH{1'b1}}, 1'b0, {(MANT_WIDTH-1){1'b1}}};
    
    // Normal boundaries
    POS_MIN_NORM = {{1'b0}, {{(EXP_WIDTH-1){1'b0}}, 1'b1}, {MANT_WIDTH{1'b0}}};
    NEG_MIN_NORM = {{1'b1}, {{(EXP_WIDTH-1){1'b0}}, 1'b1}, {MANT_WIDTH{1'b0}}};
    POS_MAX_NORM = {{1'b0}, {{(EXP_WIDTH-1){1'b1}}, 1'b0}, {MANT_WIDTH{1'b1}}};
    NEG_MAX_NORM = {{1'b1}, {{(EXP_WIDTH-1){1'b1}}, 1'b0}, {MANT_WIDTH{1'b1}}};
    
    // Subnormal boundaries
    POS_MIN_SUB  = {{1'b0}, {EXP_WIDTH{1'b0}}, {{(MANT_WIDTH-1){1'b0}}, 1'b1}};
    NEG_MIN_SUB  = {{1'b1}, {EXP_WIDTH{1'b0}}, {{(MANT_WIDTH-1){1'b0}}, 1'b1}};
    POS_MAX_SUB  = {{1'b0}, {EXP_WIDTH{1'b0}}, {MANT_WIDTH{1'b1}}};
    NEG_MAX_SUB  = {{1'b1}, {EXP_WIDTH{1'b0}}, {MANT_WIDTH{1'b1}}};
    
    // One and Two (using bias = 2^(EXP_WIDTH-1) - 1)
    // For FP16: bias=15, exp(1.0)=15, exp(2.0)=16
    // For BF16: bias=127, exp(1.0)=127, exp(2.0)=128
    POS_ONE      = {{1'b0}, get_exponent(2**(EXP_WIDTH-1)-1), {MANT_WIDTH{1'b0}}};
    NEG_ONE      = {{1'b1}, get_exponent(2**(EXP_WIDTH-1)-1), {MANT_WIDTH{1'b0}}};
    POS_TWO      = {{1'b0}, get_exponent(2**(EXP_WIDTH-1)), {MANT_WIDTH{1'b0}}};
    NEG_TWO      = {{1'b1}, get_exponent(2**(EXP_WIDTH-1)), {MANT_WIDTH{1'b0}}};
    
    tb_test_case = "EDGE_CASES";
    $display("Running explicit edge case tests...");
    
    // Division by zero
    tb_test_case = "ZERO_CASES";
    apply_vector(POS_ONE, POS_ZERO, POS_INF);
    apply_vector(POS_ZERO, POS_ONE, POS_ZERO);
    apply_vector(POS_ZERO, POS_ZERO, QNAN);
    
    // Infinity cases
    tb_test_case = "INF_CASES";
    apply_vector(POS_INF, POS_ONE, POS_INF);
    apply_vector(POS_ONE, POS_INF, POS_ZERO);
    apply_vector(POS_INF, POS_ZERO, POS_INF);
    apply_vector(POS_ZERO, POS_INF, POS_ZERO);
    apply_vector(POS_INF, POS_INF, QNAN);
    
    // NaN propagation
    tb_test_case = "NAN_PROPAGATION";
    apply_vector(QNAN, POS_ONE, QNAN);
    apply_vector(POS_ONE, QNAN, QNAN);
    apply_vector(QNAN, QNAN, QNAN);
    apply_vector(SNAN, POS_ONE, QNAN);
    apply_vector(QNAN, POS_INF, QNAN);
    apply_vector(POS_INF, QNAN, QNAN);
    apply_vector(QNAN, POS_ZERO, QNAN);
    apply_vector(POS_ZERO, QNAN, QNAN);
    
    // Normal boundaries
    tb_test_case = "NORM_BOUNDARY";
    apply_vector(POS_MAX_NORM, POS_ONE, POS_MAX_NORM);
    apply_vector(POS_MIN_NORM, POS_ONE, POS_MIN_NORM);
    apply_vector(POS_MAX_NORM, POS_MAX_NORM, POS_ONE);
    apply_vector(POS_MIN_NORM, POS_MIN_NORM, POS_ONE);

    // Subnormal boundaries
    tb_test_case = "SUBNORM_BOUNDARY";
    apply_vector(POS_MIN_SUB, POS_ONE, POS_ZERO);
    apply_vector(POS_MAX_SUB, POS_ONE, POS_ZERO);
    apply_vector(POS_MIN_SUB, POS_TWO, POS_ZERO);
    apply_vector(POS_ONE, POS_MAX_NORM, POS_ZERO);
    
    // Overflow
    tb_test_case = "OVERFLOW";
    apply_vector(POS_MAX_NORM, POS_MIN_SUB, POS_INF);
    apply_vector(NEG_MAX_NORM, POS_MIN_SUB, NEG_INF);
    
    $display("Edge case tests completed");
  end
  endtask

  //-----------------------------------------------
  // Main test sequence
  //-----------------------------------------------
  initial begin
    // Display configuration
    $display("\n========== TESTBENCH CONFIGURATION ==========");
    $display("Format:       %s", (EXP_WIDTH == 5) ? "FP16" : (EXP_WIDTH == 8) ? "BF16" : "CUSTOM");
    $display("EXP_WIDTH:    %0d", EXP_WIDTH);
    $display("MANT_WIDTH:   %0d", MANT_WIDTH);
    $display("TOTAL_WIDTH:  %0d", WIDTH);
    $display("=============================================\n");
    
    // Init handshake signals
    divif.in.valid_in = 0;
    divif.in.ready_out = 0;
    divif.in.operand1 = 0;
    divif.in.operand2 = 0;
    errors = 0;
    normal_tests = 0;
    subnormal_input_tests = 0;
    subnormal_output_tests = 0;
    edge_tests = 0;

    // Power-on reset test
    tb_test_case = "POWER_ON_RESET";
    $display("Running power-on reset test...");
    
    @(posedge CLK);
    if (divif.out.valid_out !== 0) begin
      $display("ERROR @%0t [POWER_ON_RESET]: valid_out should be 0 during reset, got %b", 
                $time, divif.out.valid_out);
      errors++;
    end
    if (divif.out.ready_in !== 0) begin
      $display("ERROR @%0t [POWER_ON_RESET]: ready_in should be 0 during reset, got %b", 
                $time, divif.out.ready_in);
      errors++;
    end
    
    if (errors == 0) begin
      $display("Power-on reset test passed");
    end
    
    #20 nRST = 1;
    #20;  // Settle
    
    // Check that ready_in goes high after reset
    @(posedge CLK);
    if (divif.out.ready_in !== 1) begin
      $display("ERROR @%0t [POST_RESET]: ready_out should be 1 after reset, got %b", 
                $time, divif.out.ready_in);
      errors++;
    end

    // Run all test categories (adjust filenames for BF16 if needed)
    if (EXP_WIDTH == 5 && MANT_WIDTH == 10) begin
      // FP16 test files
      run_file_tests("testcases/vdiv_fp16_normal_tests_10K.csv", "NORMAL_TESTS");
      normal_tests = errors;

      run_file_tests("testcases/vdiv_fp16_subnormal_input_tests_10K.csv", "SUBNORMAL_INPUT_TESTS");
      subnormal_input_tests = errors - normal_tests;

      run_file_tests("testcases/vdiv_fp16_subnormal_output_tests_10K.csv", "SUBNORMAL_OUTPUT_TESTS");
      subnormal_output_tests = errors - normal_tests - subnormal_input_tests;
    end else if (EXP_WIDTH == 8 && MANT_WIDTH == 7) begin
      // BF16 test files (if available)
      run_file_tests("testcases/vdiv_bf16_normal_tests_10K.csv", "BF16_NORMAL_TESTS");
      normal_tests = errors;

      run_file_tests("testcases/vdiv_bf16_subnormal_input_tests_10K.csv", "BF16_SUBNORMAL_INPUT_TESTS");
      subnormal_input_tests = errors - normal_tests;

      run_file_tests("testcases/vdiv_bf16_subnormal_output_tests_10K.csv", "BF16_SUBNORMAL_OUTPUT_TESTS");
      subnormal_output_tests = errors - normal_tests - subnormal_input_tests;
    end else begin
      $display("INFO: No file-based tests available for this custom format");
    end

    run_edge_case_tests();

    // Summary
    $display("\n========== TEST SUMMARY ==========");
    $display("Normal tests errors:           %0d", normal_tests);
    $display("Subnormal input tests errors:  %0d", subnormal_input_tests);
    $display("Subnormal output tests errors: %0d", subnormal_output_tests);
    $display("Edge case tests errors:        %0d", errors - (normal_tests + subnormal_input_tests + subnormal_output_tests));
    $display("Total errors:                  %0d", errors);
    $display("==================================\n");
    
    if (errors == 0)
      $display("*** ALL TESTS PASSED ***");
    else
      $display("*** TEST FAILED: %0d total errors ***", errors);
    
    $stop;
  end
endmodule