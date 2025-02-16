`timescale 1ns / 1ps

module tb_ramulator;
    import "DPI-C" function void dpi_init_ramulator();
    import "DPI-C" function void dpi_send_memory_request(longint addr, int is_write);
    import "DPI-C" function int dpi_is_request_done();
    import "DPI-C" function longint dpi_get_memory_data();
    import "DPI-C" function void dpi_tick_ramulator();

    // Simulation parameters
    int i;
    logic clk;
    logic reset;

    // Clock generation
    always #5 clk = ~clk;

    initial begin
        clk = 0;
        reset = 1;
        #10 reset = 0;

        // Initialize Ramulator
        dpi_init_ramulator();

        // Test Case 1: Write Request
        $display("[TEST] Sending Write Request to Address 0x1000");
        dpi_send_memory_request(64'h1000, 1);
        dpi_tick_ramulator();
        
        // Test Case 2: Read Request
        $display("[TEST] Sending Read Request to Address 0x1000");
        dpi_send_memory_request(64'h1000, 0);
        while (!dpi_is_request_done()) begin
            dpi_tick_ramulator();
        end
        $display("[RESULT] Read Data: %h", dpi_get_memory_data());

        // Test Case 3: Multiple Requests
        $display("[TEST] Sending Multiple Read Requests");
        for (i = 0; i < 5; i = i + 1) begin
            dpi_send_memory_request(64'h2000 + (i * 8), 0);
        end
        while (!dpi_is_request_done()) begin
            dpi_tick_ramulator();
        end
        for (i = 0; i < 5; i = i + 1) begin
            $display("[RESULT] Read Data %d: %h", i, dpi_get_memory_data());
        end

        $display("[TEST] Simulation completed.");
        $finish;
    end
endmodule
