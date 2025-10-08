`include "vreduction_if.vh"
`include "vector_types.vh"
`timescale 1ns/1ps

module vreduction_tb;
    import vector_pkg::*;
    parameter int WIDTH        = 16;
    parameter int NUM_ELEMENTS = 32;
    parameter int PERIOD       = 10;
    logic CLK = 0, nRST;

    // Clock generation
    always #(PERIOD/2) CLK = ~CLK;

    // DUT interface and instance
    vreduction_if #(.LANES(WIDTH)) vruif();
    vreduction #(.WIDTH(WIDTH)) dut (
        .CLK(CLK),
        .nRST(nRST),
        .vruif(vruif)
    );

    // ------------------------------------------------------------
    // Task: display vector output
    // ------------------------------------------------------------
    task display_vector();
        begin
            $display("Vector output:");
            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                $display("  [%0d] = 0x%04h", i, vruif.vector_output[i]);
            end
        end
    endtask

    // ------------------------------------------------------------
    // Test Sequence
    // ------------------------------------------------------------
    initial begin
        // Reset
        nRST = 0;
        vruif.input_valid   = 0;
        vruif.broadcast     = 0;
        vruif.clear         = 0;
        vruif.imm           = 0;
        vruif.reduction_type = 2'b00; // MAX
        
        // Initialize lane_input with simple incrementing pattern
        for (int i = 0; i < WIDTH; i++) begin
            vruif.lane_input[i] = 16'h3C00 + i; // FP16: roughly 1.0, 1.0+ε, ...
        end
        
        // Initialize vector_input to all 0xAAAA (distinctive pattern)
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            vruif.vector_input[i] = 16'hAAAA;
        end
        
        @(posedge CLK);
        @(posedge CLK);
        nRST = 1;
        @(posedge CLK);

        // Test 1: BROADCAST - all elements should get reduction result
        $display("Test 1: BROADCAST MODE");
        $display("Expected: All 32 elements = reduction result (max of lane_input)");
        
        vruif.broadcast = 1;
        vruif.clear     = 0;
        vruif.imm       = 0;
        vruif.input_valid = 1;
        @(posedge CLK);
        vruif.input_valid = 0;
        
        wait(vruif.output_valid);
        @(posedge CLK);
        display_vector();

        $display("Test 2: PARTIAL WRITE (imm=5, no clear)");
        $display("Expected: Index 5 = reduction result, others = previous output (from Test 1)");
        
        // Keep vector_input as-is (will read from vector_output in RTL)
        vruif.broadcast = 0;
        vruif.clear     = 0;
        vruif.imm       = 5;
        vruif.input_valid = 1;
        @(posedge CLK);
        vruif.input_valid = 0;
        
        wait(vruif.output_valid);
        @(posedge CLK);
        display_vector();

        $display("Test 3: PARTIAL WRITE (imm=7, with clear)");
        $display("Expected: Index 7 = reduction result, all others = 0x0000");
        
        vruif.broadcast = 0;
        vruif.clear     = 1;
        vruif.imm       = 7;
        vruif.input_valid = 1;
        @(posedge CLK);
        vruif.input_valid = 0;
        
        wait(vruif.output_valid);
        @(posedge CLK);
        display_vector();

        $display("Test 4: PARTIAL WRITE (imm=10, no clear)");
        $display("Expected: Index 10 = reduction result, index 7 still has old value, others = 0");
        
        vruif.broadcast = 0;
        vruif.clear     = 0;
        vruif.imm       = 10;
        vruif.input_valid = 1;
        @(posedge CLK);
        vruif.input_valid = 0;
        
        wait(vruif.output_valid);
        @(posedge CLK);
        display_vector();

        @(posedge CLK)
        $finish;
    end

endmodule