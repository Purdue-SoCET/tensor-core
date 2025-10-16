`include "vreduction_if.vh"
`include "vector_types.vh"
`include "vaddsub_if.vh"
`timescale 1ns/1ns

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
    vreduction #(.LANES(WIDTH)) dut (
        .CLK(CLK),
        .nRST(nRST),
        .vruif(vruif)
    );

    // Adder for verification
    vaddsub_if as_if ();
    vaddsub adder (CLK, nRST, as_if);

    // ------------------------------------------------------------
    // Helper tasks and types
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
        vruif.vector_input   = input_vector;
        vruif.lane_input     = input_vector[WIDTH-1:0];
        vruif.reduction_type = op;
        vruif.broadcast      = broadcast;
        vruif.clear          = clear;
        vruif.input_valid    = valid_data_input;
        vruif.imm            = index;
        @(posedge CLK);
    endtask

    task calculate_result(
        input  fp16_t [NUM_ELEMENTS-1:0] input_vector,
        input  logic [1:0] op,
        input  logic broadcast,
        input  logic clear,
        input  logic [4:0] index,
        output fp16_t [NUM_ELEMENTS-1:0] output_vector
    );
        fp16_t reduction_output;
        casez (op)
            2'b00: reduction_output = find_max(input_vector[WIDTH-1:0]);
            2'b01: reduction_output = find_min(input_vector[WIDTH-1:0]);
            2'b1?: sum_vector(input_vector[WIDTH-1:0], reduction_output);
        endcase

        if (broadcast) begin
            for (int i = 0; i < NUM_ELEMENTS; i++)
                output_vector[i] = reduction_output;
        end else if (clear) begin
            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                if (i == index)
                    output_vector[i] = reduction_output;
                else
                    output_vector[i] = 16'h0000;
            end
        end else begin
            for (int i = 0; i < NUM_ELEMENTS; i++)
                output_vector[i] = input_vector[i];
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
        as_if.enable = 1'b1;
        as_if.sub = 1'b0;
        #0;
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

    // ------------------------------------------------------------
    // File input (AI-generated helper)
    // ------------------------------------------------------------
    task read_vectors_from_file(
    input  string filename,
    output fp16_t [NUM_ELEMENTS-1:0] vectors[],
    output logic [1:0] operations[],
    output logic       broadcasts[],
    output logic       clears[],
    output logic [4:0] indexes[],
    output int         num_vectors
);
    integer file_handle;
    string line;
    int status;
    int line_count;
    string hex_str;
    int comma_pos;
    int start_pos;
    int op_value;
    int broadcast_value;
    int clear_value;
    int idx_value;

    // Open the file
    file_handle = $fopen(filename, "r");
    if (file_handle == 0) begin
        $display("ERROR: Could not open input file: %s", filename);
        $finish;
    end

    // First pass: count lines
    line_count = 0;
    while (!$feof(file_handle)) begin
        status = $fgets(line, file_handle);
        if (status != 0 && line != "") line_count++;
    end

    $fclose(file_handle);
    num_vectors = line_count;

    if (num_vectors == 0) begin
        $display("WARNING: No vectors found in file: %s", filename);
        return;
    end

    // Allocate arrays
    vectors     = new[num_vectors];
    operations  = new[num_vectors];
    broadcasts  = new[num_vectors];
    clears      = new[num_vectors];
    indexes     = new[num_vectors];

    // Second pass: read data
    file_handle = $fopen(filename, "r");
    line_count  = 0;

    while (!$feof(file_handle) && line_count < num_vectors) begin
        status = $fgets(line, file_handle);
        if (status == 0 || line == "") continue;

        start_pos = 0;

        // Parse NUM_ELEMENTS FP16 values
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            comma_pos = -1;
            for (int j = start_pos; j < line.len(); j++) begin
                if (line[j] == ",") begin
                    comma_pos = j;
                    break;
                end
            end

            if (comma_pos == -1)
                hex_str = line.substr(start_pos, line.len()-1);
            else
                hex_str = line.substr(start_pos, comma_pos-1);

            hex_str = strip_whitespace(hex_str);
            if (hex_str.len() > 0) begin
                status = $sscanf(hex_str, "%h", vectors[line_count][i]);
                if (status != 1) begin
                    $display("WARNING: Could not parse hex value '%s' at line %0d, element %0d", 
                             hex_str, line_count+1, i);
                    vectors[line_count][i] = 16'h0000;
                end
            end else
                vectors[line_count][i] = 16'h0000;

            start_pos = comma_pos + 1;
            if (comma_pos == -1) break;
        end

        // -------- Parse Operation --------
        comma_pos = -1;
        for (int j = start_pos; j < line.len(); j++) begin
            if (line[j] == ",") begin
                comma_pos = j;
                break;
            end
        end

        if (comma_pos != -1)
            hex_str = line.substr(start_pos, comma_pos-1);
        else
            hex_str = line.substr(start_pos, line.len()-1);

        hex_str = strip_whitespace(hex_str);
        status = $sscanf(hex_str, "%d", op_value);
        if (status == 1 && op_value >= 0 && op_value <= 2)
            operations[line_count] = op_value[1:0];
        else begin
            $display("WARNING: Invalid operation '%s' at line %0d, defaulting to 0 (MAX)", 
                     hex_str, line_count+1);
            operations[line_count] = 2'b00;
        end

        // -------- Parse Broadcast --------
        start_pos = comma_pos + 1;
        comma_pos = -1;
        for (int j = start_pos; j < line.len(); j++) begin
            if (line[j] == ",") begin
                comma_pos = j;
                break;
            end
        end

        if (comma_pos != -1)
            hex_str = line.substr(start_pos, comma_pos-1);
        else
            hex_str = line.substr(start_pos, line.len()-1);

        hex_str = strip_whitespace(hex_str);
        status = $sscanf(hex_str, "%d", broadcast_value);
        if (status == 1 && (broadcast_value == 0 || broadcast_value == 1))
            broadcasts[line_count] = broadcast_value;
        else begin
            $display("WARNING: Invalid broadcast value '%s' at line %0d, defaulting to 0", 
                     hex_str, line_count+1);
            broadcasts[line_count] = 1'b0;
        end

        // -------- Parse Clear --------
        start_pos = comma_pos + 1;
        comma_pos = -1;
        for (int j = start_pos; j < line.len(); j++) begin
            if (line[j] == ",") begin
                comma_pos = j;
                break;
            end
        end

        if (comma_pos != -1)
            hex_str = line.substr(start_pos, comma_pos-1);
        else
            hex_str = line.substr(start_pos, line.len()-1);

        hex_str = strip_whitespace(hex_str);
        status = $sscanf(hex_str, "%d", clear_value);
        if (status == 1 && (clear_value == 0 || clear_value == 1))
            clears[line_count] = clear_value;
        else begin
            $display("WARNING: Invalid clear value '%s' at line %0d, defaulting to 0", 
                     hex_str, line_count+1);
            clears[line_count] = 1'b0;
        end

        // -------- Parse Index --------
        start_pos = comma_pos + 1;
        if (start_pos < line.len()) begin
            hex_str = line.substr(start_pos, line.len()-1);
            hex_str = strip_whitespace(hex_str);
            status = $sscanf(hex_str, "%d", idx_value);
            if (status == 1 && idx_value >= 0 && idx_value < 32)
                indexes[line_count] = idx_value[4:0];
            else begin
                $display("WARNING: Invalid index '%s' at line %0d, defaulting to 0", 
                         hex_str, line_count+1);
                indexes[line_count] = 5'd0;
            end
        end else begin
            $display("WARNING: No index specified at line %0d, defaulting to 0", line_count+1);
            indexes[line_count] = 5'd0;
        end

        line_count++;
    end

    $fclose(file_handle);
    $display("Successfully read %0d vectors from %s", num_vectors, filename);
endtask

    
    function automatic string strip_whitespace(string s);
        string result = "";
        for (int i = 0; i < s.len(); i++)
            if (s[i] != " " && s[i] != "\t" && s[i] != "\n" && s[i] != "\r")
                result = {result, s[i]};
        return result;
    endfunction

    // ------------------------------------------------------------
    // Test setup and execution logic
    // ------------------------------------------------------------
    parameter int NUM_TESTS = 2;
    reduction_tv_t test_vecs[];
    fp16_t [NUM_ELEMENTS-1:0] expected_results[];
    int current_expected_index;
    integer file;

    fp16_t [NUM_ELEMENTS-1:0] file_vectors[];
    logic [1:0] file_operations[];
    logic [4:0] indexes[];
    logic broadcasts[];
    logic clears[];
    int num_file_vectors;

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

        read_vectors_from_file("vector.txt", file_vectors, file_operations, broadcasts, clears, indexes, num_file_vectors);
        
        test_vecs = new[num_file_vectors];
        expected_results = new[num_file_vectors];

        for (int i = 0; i < num_file_vectors; i++) begin
            test_vecs[i].tv_input_vector = file_vectors[i];
            test_vecs[i].tv_op = file_operations[i];
            test_vecs[i].tv_broadcast = broadcasts[i];
            test_vecs[i].tv_clear = clears[i];
            test_vecs[i].tv_valid_data_input = 1'b1;
            test_vecs[i].tv_index = indexes[i];
        end

        for (int i = 0; i < num_file_vectors; i++) begin
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

        for (int i = 0; i < num_file_vectors; i++) begin
            set_DUT_inputs(
                test_vecs[i].tv_input_vector,
                test_vecs[i].tv_op,
                test_vecs[i].tv_broadcast,
                test_vecs[i].tv_clear,
                1'b1,
                test_vecs[i].tv_index
            );
        end

        clear();
    end

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
            if (current_expected_index >= num_file_vectors) begin
                $fclose(file);
                $finish;
            end
        end
    end
endmodule
