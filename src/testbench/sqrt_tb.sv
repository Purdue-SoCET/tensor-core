`include "sqrt_if.vh"
`include "vector_types.vh"
`timescale 1 ns / 1 ns

module sqrt_tb;
    import vector_pkg::*;
    
    localparam MULT_LATENCY = 2;

    // Signals
    logic CLK, nRST;

    // Interface instantiation
    sqrt_if srif();
    
    // Instantiate DUT
    sqrt dut (
        .CLK(CLK),
        .nRST(nRST),
        .srif(srif)
    );

    // Clock
    initial CLK = 0;
    always #5 CLK = ~CLK;

    logic [15:0] normal_cases [0:9];
    
    initial begin
        nRST = 0;
        srif.input_val = '{sign: 1'b0, exp: 5'd0, frac: 10'd0};
        srif.valid_data_in = 0;

        #12 nRST = 1;

        normal_cases[0] = 16'h3C00; // 1.0
        normal_cases[1] = 16'h4000; // 2.0
        normal_cases[2] = 16'h4200; // 3.0
        normal_cases[3] = 16'h4400; // 4.0
        normal_cases[4] = 16'h4880; // 9.0
        normal_cases[5] = 16'h4c00; // 16.0
        normal_cases[6] = 16'h3800; // 0.5
        normal_cases[7] = 16'h3400; // 0.25
        normal_cases[8] = 16'h5640; // 100.0
        normal_cases[9] = 16'h3900; // 0.625

        $display("\n=== Starting Square Root Tests ===\n");

        for (int i = 0; i < 10; i++) begin
            // Wait for ready before sending new input
            while (!srif.ready) @(posedge CLK);
            
            @(posedge CLK);
            srif.input_val = fp16_t'(normal_cases[i]);
            srif.valid_data_in = 1;
            $display("Time %0t: Sending input 0x%h", $time, normal_cases[i]);

            @(posedge CLK);
            srif.valid_data_in = 0;
            
            // Wait for output valid
            while (!srif.valid_data_out) @(posedge CLK);
            @(posedge CLK);
            $display("Time %0t: Output received 0x%h\n", $time, srif.output_val);
        end

        repeat (10) @(posedge CLK);

        $display("\n=== Test Complete ===\n");
        $finish;
    end

    // Monitor interface signals
    always @(posedge CLK) begin
        if (srif.valid_data_in && srif.ready) begin
            $display("Time %0t: [INPUT ACCEPTED] input=0x%h", 
                     $time, srif.input_val);
        end
        
        if (srif.valid_data_out) begin
            $display("Time %0t: [OUTPUT VALID] output=0x%h", 
                     $time, srif.output_val);
        end
        
        if (!srif.ready) begin
            $display("Time %0t: [BUSY] Module not ready", $time);
        end
    end

    // Monitor internal multiplier operations
    always @(posedge CLK) begin
        if (dut.mul_done && !dut.second_pass) begin
            $display("Time %0t: [MULT1 Done] Slope=0x%h, NormMant=0x%h, Result=0x%h", 
                     $time, dut.mul_b, dut.mul_a, dut.mul_out);
        end
        
        if (dut.mul_done && dut.second_pass) begin
            $display("Time %0t: [MULT2 Done] Multiplier=0x%h, Operand=0x%h, Result=0x%h", 
                     $time, dut.mul_a, dut.mul_b, dut.mul_out);
        end
        
        if (dut.valid) begin
            $display("Time %0t: [Input Registered] exp=0x%h, frac=0x%h, slope=0x%h, intercept=0x%h",
                     $time, dut.exp, dut.frac, dut.slope, dut.intercept);
        end
    end

endmodule