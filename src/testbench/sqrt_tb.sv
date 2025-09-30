`timescale 1 ns / 1 ns
module sqrt_tb;
    // Parameters
    localparam MULT_LATENCY = 3;
    localparam TOTAL_LATENCY = 2*MULT_LATENCY + 1; // include first register stage

    // Signals
    logic CLK, nRST;
    logic [15:0] input_val;
    logic [15:0] output_val;
    logic valid_data;

    logic input_valid;

    // Instantiate the DUT
    sqrt dut (
        .CLK(CLK),
        .nRST(nRST),
        .input_val(input_val),
        .output_val(output_val),
        .valid_data(valid_data)
    );

    // Clock generation
    initial CLK = 0;
    always #5 CLK = ~CLK; // 100 MHz clock

    // Test stimulus
    initial begin
        nRST = 0;
        input_val = 16'h0000;
        input_valid = 0;

        #12 nRST = 1; // release reset

        // Apply a single test value: 2.0 in FP16 (0x4000)
        @(posedge CLK);
        input_val = 16'h4000;
        input_valid = 1;

        @(posedge CLK);
        input_valid = 0; // single-cycle valid pulse

        // Wait for full pipeline latency
        repeat (TOTAL_LATENCY + 2) @(posedge CLK);

        $display("Input: 0x%h, Output: 0x%h, Valid: %b", input_val, output_val, valid_data);

        $finish;
    end
endmodule