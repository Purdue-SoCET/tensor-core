`timescale 1ns/1ps

module reduction_tree_tb;

    localparam LANES = 16;

    // Signals
    logic CLK;
    logic nRST;
    logic [15:0] data_in [LANES-1:0];
    logic [1:0]  alu_op;
    logic        valid_in;
    logic [15:0] data_out;
    logic        valid_out;

    // DUT instantiation
    reduction_tree #(
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
    initial CLK = 0;
    always #5 CLK = ~CLK;

    initial begin
        nRST = 0;
        alu_op = 2'b10; // Sum operation
        valid_in = 0;

        // Apply reset
        #12;
        nRST = 1;

        // ----------------------
        // Cycle 1: send vector 1
        // ----------------------
        valid_in = 1;
        data_in = '{16'h3C00,16'h4000,16'h4200,16'h4400,16'h4500,16'h4600,16'h4700,16'h4800,
                    16'h4880,16'h4900,16'h4980,16'h4A00,16'h4A80,16'h4B00,16'h4B80,16'h4C00};
        @(posedge CLK);

        // ----------------------
        // Cycle 2: send vector 2
        // ----------------------
        data_in = '{16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,
                    16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000};
        @(posedge CLK);

        // Stop sending inputs
        valid_in = 0;

        // Flush pipeline
        repeat (10) @(posedge CLK);

        $finish;
    end

    // Monitor outputs
    always_ff @(posedge CLK) begin
        if (valid_out) begin
            $display("%0h", data_out);
        end
    end

endmodule
