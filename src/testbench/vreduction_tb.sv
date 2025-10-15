`include "vreduction_if.vh"
`include "vector_types.vh"
`include "vaddsub_if.vh"
`timescale 1ns/1ns

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

    // Adder for verification
    vaddsub_if as_if ();
    vaddsub adder (CLK, nRST, as_if);

    // ------------------------------------------------------------
    // Helper tasks
    // ------------------------------------------------------------
    typedef struct packed {
        fp16_t [NUM_ELEMENTS-1:0] tv_input_vector;
        logic [1:0] tv_op;
        logic tv_broadcast;
        logic tv_clear;
        logic tv_valid_data_input;
        logic [4:0] tv_index;
    } reduction_tv_t;

    task set_DUT_inputs(
        input fp16_t [NUM_ELEMENTS-1:0] input_vector,
        input logic [1:0] op,
        input logic broadcast,
        input logic clear,
        input logic valid_data_input,
        input logic [4:0] index
    );
        vruif.vector_input = input_vector;
        vruif.lane_input   = input_vector[WIDTH-1:0];
        vruif.reduction_type = op;
        vruif.broadcast    = broadcast;
        vruif.clear        = clear;
        vruif.input_valid  = valid_data_input;
        vruif.imm          = index;
        @(posedge CLK);
    endtask

    task calculate_result(
        input fp16_t [NUM_ELEMENTS-1:0] input_vector,
        input logic [1:0] op,
        input logic broadcast,
        input logic clear,
        input logic [4:0] index,
        output fp16_t [NUM_ELEMENTS-1:0] output_vector
    );
        fp16_t reduction_output;
        casez (op)
            2'b00: reduction_output = find_max(input_vector[WIDTH-1:0]);
            2'b01: reduction_output = find_min(input_vector[WIDTH-1:0]);
            2'b1?: sum_vector(input_vector[WIDTH-1:0], reduction_output);
        endcase

        if (broadcast) begin
            output_vector = {NUM_ELEMENTS{reduction_output}};
        end else if (clear) begin
            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                if (i == index)
                    output_vector[i] = reduction_output;
                else
                    output_vector[i] = 16'h0000;
            end
        end else begin
            output_vector = input_vector;
            output_vector[index] = reduction_output;
        end
    endtask

    function automatic fp16_t find_max(fp16_t [WIDTH-1:0] tree_inputs);
        fp16_t max_val = tree_inputs[0];
        for (int i = 1; i < WIDTH; i++)
            if (tree_inputs[i] > max_val)
                max_val = tree_inputs[i];
        return max_val;
    endfunction

    function automatic fp16_t find_min(fp16_t [WIDTH-1:0] tree_inputs);
        fp16_t min_val = tree_inputs[0];
        for (int i = 1; i < WIDTH; i++)
            if (tree_inputs[i] < min_val)
                min_val = tree_inputs[i];
        return min_val;
    endfunction

    task fp16_add(input fp16_t a, input fp16_t b, output fp16_t out);
        as_if.port_a = a;
        as_if.port_b = b;
        #1;
        out = as_if.out;
    endtask

    task sum_vector(input fp16_t [WIDTH-1:0] values, output fp16_t total);
        fp16_t temp_sum;
        total = 16'h0;
        for (int i = 0; i < WIDTH; i++) begin
            fp16_add(total, values[i], temp_sum);
            total = temp_sum;
        end
    endtask

    task clear();
        vruif.input_valid    = 0;
        vruif.broadcast      = 0;
        vruif.clear          = 0;
        vruif.imm            = 0;
        vruif.reduction_type = 2'b00;
    endtask

    parameter int NUM_TESTS = 2;
    reduction_tv_t test_vecs[NUM_TESTS];
    fp16_t [NUM_ELEMENTS-1:0] expected_results[NUM_TESTS];
    int current_expected_index;
    integer file;

    initial begin
        file = $fopen("vreduction_tb_results.txt", "w");
        if (file == 0) begin
            $display("ERROR: Could not open output file.");
            $finish;
        end

        nRST = 0;
        current_expected_index = 0;
        clear();
        as_if.enable = 'b1;

        // Test 0: broadcast MAX
        test_vecs[0].tv_input_vector = '{
            16'h5000, 16'h4fc0, 16'h4f80, 16'h4f40,
            16'h4f00, 16'h4ec0, 16'h4e80, 16'h4e40,
            16'h4e00, 16'h4dc0, 16'h4d80, 16'h4d40,
            16'h4d00, 16'h4cc0, 16'h4c80, 16'h4c40,
            16'h4C00, 16'h4b80, 16'h4b00, 16'h4a80,
            16'h4a00, 16'h4980, 16'h4900, 16'h4880,
            16'h4800, 16'h4700, 16'h4600, 16'h4500,
            16'h4400, 16'h4200, 16'h4000, 16'h3c00
        };

        test_vecs[0].tv_op = 2'b00; // MAX
        test_vecs[0].tv_broadcast = 1;
        test_vecs[0].tv_clear = 0;
        test_vecs[0].tv_valid_data_input = 1'b1;
        test_vecs[0].tv_index = 5'd5;

        test_vecs[1].tv_input_vector = '{
            16'h5000, 16'h4fc0, 16'h4f80, 16'h4f40,
            16'h4f00, 16'h4ec0, 16'h4e80, 16'h4e40,
            16'h4e00, 16'h4dc0, 16'h4d80, 16'h4d40,
            16'h4d00, 16'h4cc0, 16'h4c80, 16'h4c40,
            16'h4C00, 16'h4b80, 16'h4b00, 16'h4a80,
            16'h4a00, 16'h4980, 16'h4900, 16'h4880,
            16'h4800, 16'h4700, 16'h4600, 16'h4500,
            16'h4400, 16'h4200, 16'h4000, 16'h3c00
        };

        test_vecs[1].tv_op = 2'b01; // MIN
        test_vecs[1].tv_broadcast = 1;
        test_vecs[1].tv_clear = 0;
        test_vecs[1].tv_valid_data_input = 1'b1;
        test_vecs[1].tv_index = 5'd5;

        // Precompute expected results
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

        // Send test 0
        set_DUT_inputs(
            test_vecs[0].tv_input_vector,
            test_vecs[0].tv_op,
            test_vecs[0].tv_broadcast,
            test_vecs[0].tv_clear,
            1'b1,
            test_vecs[0].tv_index
        );
        // Send test 2
        set_DUT_inputs(
            test_vecs[1].tv_input_vector,
            test_vecs[1].tv_op,
            test_vecs[1].tv_broadcast,
            test_vecs[1].tv_clear,
            1'b1,
            test_vecs[1].tv_index
        );

        clear();




    end

    //Chat wrote the file IO stuff to save me time
    always @(posedge CLK) begin
        automatic string expected_line;
        automatic string actual_line;

        if (vruif.output_valid) begin
            expected_line = "";
            actual_line = "";

            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                expected_line = {expected_line, $sformatf("%04h ", expected_results[current_expected_index][i])};
                actual_line   = {actual_line,   $sformatf("%04h ", vruif.vector_output[i])};
            end

            if (vruif.vector_output === expected_results[current_expected_index]) begin
                $display("Test Number %0d: PASS", current_expected_index);
                $display("Expected: %s", expected_line);
                $display("Actual  : %s", actual_line);

                $fdisplay(file, "Test Number %0d: PASS", current_expected_index);
                $fdisplay(file, "Expected: %s", expected_line);
                $fdisplay(file, "Actual  : %s", actual_line);
            end else begin
                $display("Test Number %0d: FAIL", current_expected_index);
                $display("Expected: %s", expected_line);
                $display("Actual  : %s", actual_line);

                $fdisplay(file, "Test Number %0d: FAIL", current_expected_index);
                $fdisplay(file, "Expected: %s", expected_line);
                $fdisplay(file, "Actual  : %s", actual_line);
            end

            current_expected_index++;
            if (current_expected_index >= NUM_TESTS) begin
                $fclose(file);
                $finish;
            end
        end
    end
endmodule
