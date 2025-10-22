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
        data_in = '{default: 16'h0000};

        // Apply reset
        #12;
        nRST = 1;
        #10;

        // ----------------------
        // Burst: Send 4 vectors back-to-back
        // ----------------------
        $display("Starting burst of 4 vectors");
        
        // Vector 1: Mixed values
        valid_in = 1;
        alu_op = 2'b10; // VR_SUM
        data_in = '{16'h3C00,16'h4000,16'h4200,16'h4400,16'h4500,16'h4600,16'h4700,16'h4800,
                    16'h4880,16'h4900,16'h4980,16'h4A00,16'h4A80,16'h4B00,16'h4B80,16'h4C00};
        @(posedge CLK);

        // Vector 2: All 2.0
        data_in = '{16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,
                    16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000,16'h4000};
        @(posedge CLK);

        // Vector 3: Mixed for MAX
        alu_op = 2'b00; // VR_MAX
        data_in = '{16'h3C00,16'h4000,16'h4200,16'h4400,16'h4500,16'h4600,16'h4700,16'h4800,
                    16'h4880,16'h4900,16'h4980,16'h4A00,16'h4A80,16'h4B00,16'h4B80,16'h4C00};
        @(posedge CLK);

        // Vector 4: Mixed for MIN
        alu_op = 2'b01; // VR_MIN
        data_in = '{16'h3C00,16'h4000,16'h4200,16'h4400,16'h4500,16'h4600,16'h4700,16'h4800,
                    16'h4880,16'h4900,16'h4980,16'h4A00,16'h4A80,16'h4B00,16'h4B80,16'h4C00};
        @(posedge CLK);

        // Stop sending inputs
        valid_in = 0;

        // Wait for all results to flush through pipeline
        repeat (20) @(posedge CLK);

        $finish;
    end

    // Monitor outputs
    always_ff @(posedge CLK) begin
        if (valid_out) begin
            $display("Result: %0h", data_out);
        end
    end

endmodule