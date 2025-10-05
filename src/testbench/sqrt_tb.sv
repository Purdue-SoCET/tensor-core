`timescale 1 ns / 1 ns
module sqrt_tb;
    localparam MULT_LATENCY = 3;
    localparam TOTAL_LATENCY = 2*MULT_LATENCY + 1; // include first register stage

    // Signals
    logic CLK, nRST;
    logic [15:0] input_val;
    logic [15:0] output_val;
    logic valid_data_in;
    logic valid_data_out;

    // Instantiate DUT
    sqrt dut (
        .CLK(CLK),
        .nRST(nRST),
        .input_val(input_val),
        .valid_data_in(valid_data_in),
        .output_val(output_val),
        .valid_data_out(valid_data_out)
    );

    // Clock
    initial CLK = 0;
    always #5 CLK = ~CLK;

    logic [15:0] special_cases [0:7];
    initial begin
        nRST = 0;
        input_val = 16'h0000;
        valid_data_in = 0;

        #12 nRST = 1;

        special_cases[0] = 16'h0000; // +0
        special_cases[1] = 16'h8000; // -0
        special_cases[2] = 16'h7C00; // +inf
        special_cases[3] = 16'hFC00; // -inf
        special_cases[4] = 16'h7E00; // NaN
        special_cases[5] = 16'hFE00; // another NaN
        special_cases[6] = 16'hBC00; // negative normal
        special_cases[7] = 16'hB800; // negative subnormal

        for (int i = 0; i < 8; i++) begin
            @(posedge CLK);
            input_val = special_cases[i];
            valid_data_in = 1;

            @(posedge CLK);
            valid_data_in = 0;

        end

        repeat (TOTAL_LATENCY + 5) @(posedge CLK);

        $finish;
    end

    always @(posedge CLK) begin
        if (valid_data_out) begin
            $display("Time %0t: Output valid! Output_val = 0x%h", $time, output_val);
        end
    end
endmodule
