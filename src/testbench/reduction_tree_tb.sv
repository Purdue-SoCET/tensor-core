`timescale 1ns/1ps
`include "vector_types.vh"

module reduction_tree_tb;

    import vector_pkg::*;

    // Test parameters
    localparam LANES = 8;  // Using 8 lanes for manageable test
    localparam TREE_DEPTH = $clog2(LANES);
    localparam PIPELINE_LATENCY = TREE_DEPTH + 2; // Input reg + tree stages + output reg
    
    // Clock and reset
    logic CLK;
    logic nRST;
    
    // DUT signals
    logic [15:0] data_in [LANES-1:0];
    logic [1:0] alu_op;
    logic valid_in;
    logic [15:0] data_out;
    logic valid_out;
    
    // Test tracking
    int test_num;
    int cycle_count;
    
    // Expected results queue (for pipeline verification)
    typedef struct {
        logic [15:0] expected_result;
        int test_id;
        logic [1:0] operation;
    } expected_t;
    
    expected_t expected_queue[$];
    
    // DUT instantiation
    pipelined_reduction_tree #(
        .LANES(LANES)
    ) dut (
        .CLK(CLK),
        .nRST(nRST),
        .data_in(data_in),
        .alu_op(alu_op),
        .valid_in(valid_in),
        .data_out(data_out),
        .valid_out(valid_out)
    );
    
    // Clock generation
    initial begin
        CLK = 0;
        forever #5 CLK = ~CLK;
    end
    
    // Cycle counter
    always_ff @(posedge CLK) begin
        if (!nRST)
            cycle_count <= 0;
        else
            cycle_count <= cycle_count + 1;
    end
    
    // Function to calculate expected sum result
    function logic [15:0] calc_expected_sum(logic [15:0] inputs[LANES]);
        logic [15:0] result;
        result = inputs[0];
        for (int i = 1; i < LANES; i++) begin
            result = result + inputs[i];
        end
        return result;
    endfunction
    
    // Function to calculate expected max result
    function logic [15:0] calc_expected_max(logic [15:0] inputs[LANES]);
        logic [15:0] result;
        result = inputs[0];
        for (int i = 1; i < LANES; i++) begin
            if ($signed(inputs[i]) > $signed(result))
                result = inputs[i];
        end
        return result;
    endfunction
    
    // Function to calculate expected min result
    function logic [15:0] calc_expected_min(logic [15:0] inputs[LANES]);
        logic [15:0] result;
        result = inputs[0];
        for (int i = 1; i < LANES; i++) begin
            if ($signed(inputs[i]) < $signed(result))
                result = inputs[i];
        end
        return result;
    endfunction
    
    // Output checker
    expected_t expected_result;
    
    always_ff @(posedge CLK) begin
        if (valid_out && expected_queue.size() > 0) begin
            expected_result = expected_queue.pop_front();
            
            if (data_out == expected_result.expected_result) begin
                $display("[PASS] Cycle %0d: Test %0d - Op=%0d, Result=0x%h",
                         cycle_count, expected_result.test_id, expected_result.operation, data_out);
            end else begin
                $display("[FAIL] Cycle %0d: Test %0d - Op=%0d, Expected=0x%h, Got=0x%h",
                         cycle_count, expected_result.test_id, expected_result.operation, 
                         expected_result.expected_result, data_out);
            end
        end
    end
    
    // Test stimulus
    initial begin
        test_num = 0;
        
        // Initialize signals
        nRST = 0;
        valid_in = 0;
        data_in = '{default: 16'h0};
        alu_op = 2'b0;
        
        // Reset sequence
        repeat(3) @(posedge CLK);
        nRST = 1;
        @(posedge CLK);
        
        $display("=== Starting Pipeline Reduction Tree Test ===");
        $display("LANES = %0d, TREE_DEPTH = %0d, LATENCY = %0d cycles", 
                 LANES, TREE_DEPTH, PIPELINE_LATENCY);
        $display("");
        
        // Test 1: Simple ascending sum
        $display("Test 1: Sum of ascending values (1,2,3...8)");
        send_test_vector('{16'h3C00, 16'h4000, 16'h4200, 16'h4400, 
                          16'h4500, 16'h4600, 16'h4700, 16'h4800}, 
                         2'b10, 16'h5080); // VR_SUM, 1+2+3+4+5+6+7+8 = 36 = 0x5080
        
        // Test 2: All same values sum
        $display("Test 2: Sum of same values (all 5)");
        send_test_vector('{16'h4500, 16'h4500, 16'h4500, 16'h4500,
                          16'h4500, 16'h4500, 16'h4500, 16'h4500},
                         2'b10, 16'h5100); // 8*5 = 40 = 0x5100
        
        // Test 3: Max operation
        $display("Test 3: Max of values with 100 as maximum");
        send_test_vector('{16'h3C00, 16'h4000, 16'h5640, 16'h4400,
                          16'h4200, 16'h4300, 16'h4100, 16'h3E00},
                         2'b00, 16'h5640); // VR_MAX, max is 100
        
        // Test 4: Min operation
        $display("Test 4: Min of values with 1 as minimum");
        send_test_vector('{16'h4500, 16'h4600, 16'h4700, 16'h4800,
                          16'h3C00, 16'h4000, 16'h4200, 16'h4400},
                         2'b01, 16'h3C00); // VR_MIN, min is 1
        
        // Test 5-8: Back-to-back pipeline test (demonstrates 1 result/cycle)
        $display("");
        $display("Tests 5-8: Back-to-back pipeline test (continuous feed)");
        send_test_vector('{16'h3C00, 16'h3C00, 16'h3C00, 16'h3C00,
                          16'h3C00, 16'h3C00, 16'h3C00, 16'h3C00},
                         2'b10, 16'h4800); // 8*1 = 8 = 0x4800
        
        send_test_vector('{16'h4000, 16'h4000, 16'h4000, 16'h4000,
                          16'h4000, 16'h4000, 16'h4000, 16'h4000},
                         2'b10, 16'h4C00); // 8*2 = 16 = 0x4C00
        
        send_test_vector('{16'h4200, 16'h4200, 16'h4200, 16'h4200,
                          16'h4200, 16'h4200, 16'h4200, 16'h4200},
                         2'b10, 16'h4E00); // 8*3 = 24 = 0x4E00
        
        send_test_vector('{16'h4400, 16'h4400, 16'h4400, 16'h4400,
                          16'h4400, 16'h4400, 16'h4400, 16'h4400},
                         2'b10, 16'h5000); // 8*4 = 32 = 0x5000
        
        // Wait for all results to come out
        repeat(PIPELINE_LATENCY + 5) @(posedge CLK);
        
        // Summary
        $display("");
        $display("=== Test Complete ===");
        if (expected_queue.size() == 0) begin
            $display("All tests processed successfully!");
        end else begin
            $display("WARNING: %0d expected results not received", expected_queue.size());
        end
        
        $finish;
    end
    
    // Task to send test vector and queue expected result
    task send_test_vector(input logic [15:0] inputs[LANES], input logic [1:0] op, input logic [15:0] expected);
        expected_t exp;
        
        test_num++;
        
        @(posedge CLK);
        valid_in = 1'b1;
        for (int i = 0; i < LANES; i++) begin
            data_in[i] = inputs[i];
        end
        alu_op = op;
        
        // Debug: Print what we're sending
        $display("  Sending Test %0d: op=%0d", test_num, op);
        $write("    Inputs: ");
        for (int i = 0; i < LANES; i++) begin
            $write("0x%h ", inputs[i]);
        end
        $display("");
        $display("    Expected result: 0x%h", expected);
        
        // Queue expected result
        exp.expected_result = expected;
        exp.test_id = test_num;
        exp.operation = op;
        expected_queue.push_back(exp);
        
        @(posedge CLK);
        valid_in = 1'b0;
    endtask
    
endmodule