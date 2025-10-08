`include "vector_types.vh"
`timescale 1ns/1ns

module vbank_tb;
    import vector_pkg::*;

    // Parameters
    localparam INDEX_WIDTH  = 5;
    localparam NUM_ELEMENTS = 32;
    localparam DATA_WIDTH   = 16;
    localparam NUM_ROWS     = 32; 

    parameter PERIOD = 10;

    // DUT signals
    logic CLK = 0;
    logic ren, wen;
    logic [INDEX_WIDTH-1:0] raddr, waddr;
    vreg_t rdata, wdata;
    logic [NUM_ELEMENTS-1:0] wstrb;
    
    // Test Control Signals
    string test_case_name; 
    logic [DATA_WIDTH*NUM_ELEMENTS-1:0] expected_data;

    always #(PERIOD/2) CLK++;

    // DUT instantiation
    vbank #(
        .INDEX_WIDTH(INDEX_WIDTH),
        .NUM_ELEMENTS(NUM_ELEMENTS),
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_ROWS(NUM_ROWS)
    ) dut (
        .clk(CLK),
        .ren(ren),
        .raddr(raddr),
        .rdata(rdata),
        .wen(wen),
        .waddr(waddr),
        .wdata(wdata),
        .wstrb(wstrb)
    );

    // Helper task for clock-aligned stimulus and data check
    task set_and_check(
        input string tc_name,
        input logic _ren, 
        input logic _wen, 
        input logic [INDEX_WIDTH-1:0] _raddr, 
        input logic [INDEX_WIDTH-1:0] _waddr, 
        input logic [DATA_WIDTH*NUM_ELEMENTS-1:0] _wdata, 
        input logic [NUM_ELEMENTS-1:0] _wstrb,
        input logic check_read // Flag to check rdata in this cycle
    );
        test_case_name = tc_name;
        $display("--- Running Test: %s ---", test_case_name);
        
        ren   = _ren;
        wen   = _wen;
        raddr = _raddr;
        waddr = _waddr;
        wdata = _wdata;
        wstrb = _wstrb;
        
        @(posedge CLK);
        
        if (check_read) begin
            if (rdata !== expected_data)
                $error("Test FAILED [%s]: Data mismatch (Expected: %h, Got: %h)", test_case_name, expected_data, rdata);
            else
                $display("Test PASSED [%s]: Data verified.", test_case_name);
        end
    endtask

    // Test procedure
    initial begin
        // ====================================================================
        // LOCAL DECLARATIONS (Must be at the very top of the initial block!)
        // ====================================================================
        localparam R_W_ADDR = 5'd10;
        
        // VARIABLES that need to be declared here to follow standard Verilog
        logic [DATA_WIDTH*NUM_ELEMENTS-1:0] unique_data;
        logic [DATA_WIDTH*NUM_ELEMENTS-1:0] expected_data_val;
        
        $info("Starting vbank Testbench...");
        
        // Initialize 
        set_and_check("INIT", 0, 0, '0, '0, '0, '0, 0); 

        // ----------------------------------------------------------------
        // 1. Writing to each VREG (V0, V1, V2... V31)
        // ----------------------------------------------------------------
        $display("\n=======================================================");
        $display("1. Writing to each VREG (Loop)");
        $display("=======================================================");

        for (int i = 0; i < NUM_ROWS; i++) begin
            // Note: unique_data is declared above, not here
            // Create data where the value is based on the row index (i)
            unique_data = {NUM_ELEMENTS{DATA_WIDTH'(i + 1)}}; 
            
            // Write to vreg[i]
            set_and_check($sformatf("1A. WRITE VREG[%0d]", i), 
                        0, 1, 'z, INDEX_WIDTH'(i), unique_data, '1, 0); 
        end
        
        // De-assert controls after loop
        set_and_check("1B. CLOCK DUMMY", 0, 0, 'z, 'z, 'z, 'z, 0); 


        // ----------------------------------------------------------------
        // 2. Reading from each VREG (V0, V1, V2... V31)
        // ----------------------------------------------------------------
        $display("\n=======================================================");
        $display("2. Reading from each VREG (Loop)");
        $display("=======================================================");

        for (int i = 0; i < NUM_ROWS; i++) begin
            // Note: expected_data_val is declared above, not here
            expected_data_val = {NUM_ELEMENTS{DATA_WIDTH'(i + 1)}}; 
            expected_data = expected_data_val; // Set global expected data
            
            // Read from vreg[i]
            set_and_check($sformatf("2A. READ VREG[%0d]", i), 
                        1, 0, INDEX_WIDTH'(i), 'z, 'z, 'z, 1); 
        end
        
        // De-assert controls after loop
        set_and_check("2B. CLOCK DUMMY", 0, 0, 'z, 'z, 'z, 'z, 0); 


        // ----------------------------------------------------------------
        // 3. A Read and a Write at the same time (RAW Hazard)
        // ----------------------------------------------------------------
        $display("\n=======================================================");
        $display("3. CONCURRENT R/W (RAW Hazard)");
        $display("=======================================================");

        // Setup: Write new data (0xDEAD...) to VREG[10] and read from VREG[10] simultaneously
        // localparam R_W_ADDR = 5'd10; <-- MOVED TO TOP
        
        // Read the known OLD value (from Test 1: VREG[10] holds 0x000B...)
        // Expected value of VREG[10] is 11 (decimal) or 0x000B
        expected_data = {NUM_ELEMENTS{16'h000B}}; 
        
        // Data being written (NEW data)
        wdata = {NUM_ELEMENTS{16'hDEAD}}; 
        
        // Execute R and W concurrently 
        set_and_check("3A. R/W VREG[10] (Hazard)", 
                    1, 1, R_W_ADDR, R_W_ADDR, wdata, '1, 1);

        // Final verification that the write successfully landed
        expected_data = {NUM_ELEMENTS{16'hDEAD}};
        set_and_check("3B. VERIFY VREG[10] NEW DATA", 
                    1, 0, R_W_ADDR, 'z, 'z, 'z, 1);
        
        
        $display("\nvbank_tb: All required tests complete.");
        $finish;
    end

endmodule