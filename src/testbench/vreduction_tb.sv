`include "vreduction_if.vh"
`include "vector_types.vh"
`include "vaddsub_if.vh"
`timescale 1ns/1ps

module vreduction_tb;
    import vector_pkg::*;
    parameter int WIDTH        = 8;
    parameter int NUM_ELEMENTS = 32;
    parameter int PERIOD       = 10;
    logic CLK = 0, nRST;

    // Clock generation
    always #(PERIOD/2) CLK = ~CLK;

    // DUT interface and instance
    vreduction_if #(.LANES(WIDTH)) vruif();
    vreduction #(.LANES(WIDTH)) dut (
        .CLK(CLK),
        .nRST(nRST),
        .vruif(vruif)
    );

    //adder for verifcation
    vaddsub_if as_if ();
    vaddsub adder (CLK, nRST, as_if);


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

    typedef struct packed {
        fp16_t [NUM_ELEMENTS-1:0] tv_input_vector;
        logic [1:0] tv_op;
        logic tv_broadcast;
        logic tv_clear;
        logic tv_valid_data_input;
        logic [4:0] tv_index;
    } reduction_tv_t;

    task set_DUT_inputs( //a task that will set the inputs for the DUT
        input fp16_t [NUM_ELEMENTS-1:0] input_vector,
        input logic [1:0] op,
        input logic broadcast,
        input logic clear,
        input logic valid_data_input,
        input logic [4:0] index
        );

        vruif.vector_input = input_vector;
        vruif.lane_input = input_vector[WIDTH-1:0];
        vruif.reduction_type = op;
        vruif.broadcast = broadcast;
        vruif.clear = clear;
        vruif.input_valid = valid_data_input;
        vruif.imm = index;
        @(posedge CLK);
    endtask

    task calculate_result( //a task that will calculate the desired output vector. (ASSUMES IS REDUCING THE FIRST WIDTH INDEXES OF THE INPUTVECTOR)
        input fp16_t [NUM_ELEMENTS-1:0] input_vector,
        input logic [1:0] op,
        input logic broadcast,
        input logic clear,
        input logic [4:0] index,
        output fp16_t[NUM_ELEMENTS-1:0] output_vector
        );

        fp16_t reduction_output;

        casez (op)
            2'b00: reduction_output = find_max(input_vector[WIDTH-1:0]);
            2'b01: reduction_output = find_min(input_vector[WIDTH-1:0]);
            2'b1?: sum_vector(input_vector[WIDTH-1:0], reduction_output);
        endcase

        if (broadcast) begin
            output_vector = {NUM_ELEMENTS{reduction_output}};
        end
        else if (clear) begin
            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                if (i == index) begin
                    output_vector[i] =  reduction_output;
                end
                else begin
                    output_vector[i] = 16'h0000;
                end
            end
        end
        else begin
            output_vector = input_vector;
            output_vector[index] = reduction_output;
        end
    endtask

    function automatic fp16_t find_max(fp16_t[WIDTH-1:0] tree_inputs);
        fp16_t max_val;
        max_val = tree_inputs[0];
        for (int i = 1; i < WIDTH; i++) begin
            if (tree_inputs[i] > max_val) begin
                max_val = tree_inputs[i];
            end
        end
        return max_val;
    endfunction

    function automatic fp16_t find_min(fp16_t[WIDTH-1:0] tree_inputs);
        fp16_t min_val; 
        min_val = tree_inputs[0];
        for (int i = 1; i < WIDTH; i++) begin
            if (tree_inputs[i] < min_val) begin
                min_val = tree_inputs[i];
            end
        end
        return min_val;
    endfunction

    task fp16_add(
        input fp16_t a,
        input fp16_t b,
        output fp16_t out
    );
        as_if.port_a = a;
        as_if.port_b = b;
        #1;
        out = as_if.out;
    endtask

    task sum_vector(
        input fp16_t [WIDTH-1:0] values,
        output fp16_t total
    );
        fp16_t temp_sum;
        total = 16'h0;
        
        for (int i = 0; i < WIDTH; i++) begin
            fp16_add(total, values[i], temp_sum);
            total = temp_sum;
        end
        
    endtask

    task clear();
        vruif.input_valid   = 0;
        vruif.broadcast     = 0;
        vruif.clear         = 0;
        vruif.imm           = 0;
        vruif.reduction_type = 2'b00; // MAX
    endtask

    parameter int NUM_TESTS = 2;
    reduction_tv_t test_vecs[NUM_TESTS];
    fp16_t [NUM_ELEMENTS-1:0] expected_results[NUM_TESTS];
    int current_expected_index;
    integer file;

    initial begin
        // Reset
        file = $fopen("vreduction_tb_results.txt", "w");
        if (file == 0) begin
            $display("ERROR: Could not open output file.");
            $finish;
        end
        nRST = 0;
        current_expected_index = 0;
        clear();
        as_if.enable = 'b1;

        // Manually set ascending vector 0..31 (16-bit values)
        test_vecs[0].tv_input_vector = '{
            16'h0000, 16'h3C00, 16'h4000, 16'h4200,
            16'h4400, 16'h4500, 16'h4600, 16'h4700,
            16'h4800, 16'h4900, 16'h4A00, 16'h4B00,
            16'h4C00, 16'h4D00, 16'h4E00, 16'h4F00,
            16'h5000, 16'h5100, 16'h5200, 16'h5300,
            16'h5400, 16'h5500, 16'h5600, 16'h5700,
            16'h5800, 16'h5900, 16'h5A00, 16'h5B00,
            16'h5C00, 16'h5D00, 16'h5E00, 16'h5F00
        };

        test_vecs[0].tv_op          = 2'b00; // MAX
        test_vecs[0].tv_broadcast   = 1;
        test_vecs[0].tv_clear       = 0;
        test_vecs[0].tv_valid_data_input = 1'b1;
        test_vecs[0].tv_index       = 0; // irrelevant for broadcast


        test_vecs[1].tv_input_vector = '{
            16'h0000, 16'h3C00, 16'h4000, 16'h4200,
            16'h4400, 16'h4500, 16'h4600, 16'h4700,
            16'h4800, 16'h4900, 16'h4A00, 16'h4B00,
            16'h4C00, 16'h4D00, 16'h4E00, 16'h4F00,
            16'h5000, 16'h5100, 16'h5200, 16'h5300,
            16'h5400, 16'h5500, 16'h5600, 16'h5700,
            16'h5800, 16'h5900, 16'h5A00, 16'h5B00,
            16'h5C00, 16'h5D00, 16'h5E00, 16'h5F00
        };

        test_vecs[1].tv_op          = 2'b01; //MIN
        test_vecs[1].tv_broadcast   = 0;
        test_vecs[1].tv_clear       = 1;
        test_vecs[1].tv_valid_data_input = 1'b1;
        test_vecs[1].tv_index       = 0; // irrelevant for broadcast
        
        //precalulate the results of the reductions.
        for (int i = 0; i < NUM_TESTS; i++) begin
            calculate_result(
                test_vecs[i].tv_input_vector,
                test_vecs[i].tv_op,
                test_vecs[i].tv_broadcast,
                test_vecs[i].tv_clear,
                test_vecs[i].tv_index,
                expected_results[i]
                );
        end

        @(posedge CLK);
        nRST = 1;
        
       
        // Send first input vector
        set_DUT_inputs(
            test_vecs[0].tv_input_vector,
            test_vecs[0].tv_op,
            test_vecs[0].tv_broadcast,
            test_vecs[0].tv_clear,
            1'b1,
            test_vecs[0].tv_index
        );

        // Wait enough cycles for first operation to propagate through DUT pipeline
        @(posedge CLK);
        @(posedge CLK);

        clear();

        // Send second input vector
        set_DUT_inputs(
            test_vecs[1].tv_input_vector,
            test_vecs[1].tv_op,
            test_vecs[1].tv_broadcast,
            test_vecs[1].tv_clear,
            1'b1,
            test_vecs[1].tv_index
        );

        // Wait enough cycles for second operation to propagate
        for (int i = 0; i < 5; i++) @(posedge CLK); // adjust based on DUT latency

        clear();
    end


    always @(posedge CLK) begin
    automatic string expected_line;
    automatic string actual_line;
    automatic int i;

    if (vruif.output_valid) begin
        if (vruif.vector_output === expected_results[current_expected_index]) begin
            $display("Cycle %0d: TEST PASSED", $time/PERIOD);
            $fdisplay(file, "Cycle %0d: TEST PASSED", $time/PERIOD);
        end 
        else begin
            $display("Cycle %0d: TEST FAILED", $time/PERIOD);
            $fdisplay(file, "Cycle %0d: TEST FAILED", $time/PERIOD);

            // Build expected vector in one line
            expected_line = "";
            for (i = 0; i < NUM_ELEMENTS; i = i + 1) begin
                expected_line = {expected_line, $sformatf("%04h ", expected_results[current_expected_index][i])};
            end
            $display("Expected: %s", expected_line);
            $fdisplay(file, "Expected: %s", expected_line);

            // Build actual vector in one line
            actual_line = "";
            for (i = 0; i < NUM_ELEMENTS; i = i + 1) begin
                actual_line = {actual_line, $sformatf("%04h ", vruif.vector_output[i])};
            end
            $display("Actual  : %s", actual_line);
            $fdisplay(file, "Actual  : %s", actual_line);
        end

        current_expected_index++;

        // Close file and finish simulation after last expected result
        if (current_expected_index >= NUM_TESTS) begin
            $fclose(file);
            $finish;
        end
    end
end

endmodule