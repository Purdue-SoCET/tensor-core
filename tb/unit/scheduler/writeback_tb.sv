// Writeback unit testbench
// tahan

`timescale 1ns/1ps
`include "writeback_if.vh"

module writeback_tb;

    // Clock and Reset
    logic CLK;
    logic nRST;

    // Instantiate Interface
    writeback_if wbif();

    // DUT (Device Under Test) Instantiation
    writeback DUT (
        .CLK(CLK),
        .nRST(nRST),
        .wbif(wbif)
    );

    // Clock Generation
    always #5 CLK = ~CLK;  // 10 ns clock period

    // Test Sequence
    initial begin
        // Initialize Signals
        CLK = 0;
        nRST = 0;
        wbif.load_ready = 0;
        wbif.alu_ready = 0;
        wbif.alu_out = 0;
        wbif.dmemload = 0;
        wbif.reg_sel_alu = 0;
        wbif.reg_sel_load = 0;

        // Apply Reset
        #10 nRST = 1;  
        #10;

        // Test Case 1: ALU writes back
        wbif.alu_ready = 1;
        wbif.alu_out = 32'hADD00ADD;
        wbif.reg_sel_alu = 5'h1;
        #10;
        assert(wbif.wb_out.s_rw_en == 1);
        assert(wbif.wb_out.s_rw == 5'h1);
        assert(wbif.wb_out.s_wdata == 32'hADD00ADD);

        // Test Case 2: Load writes back
        wbif.alu_ready = 0;
        wbif.load_ready = 1;
        wbif.dmemload = 32'hDEADBEEF;
        wbif.reg_sel_load = 5'h2;
        #10;
        assert(wbif.wb_out.s_rw_en == 1);
        assert(wbif.wb_out.s_rw == 5'h2);
        assert(wbif.wb_out.s_wdata == 32'hDEADBEEF);

        // Test Case 3: Both ALU and Load ready (Load should take priority)
        wbif.alu_ready = 1;
        wbif.load_ready = 1;
        wbif.alu_out = 32'h12345678;
        wbif.dmemload = 32'hFEEDFADE;
        wbif.reg_sel_alu = 5'h3;
        wbif.reg_sel_load = 5'h4;
        #10;
        assert(wbif.wb_out.s_rw_en == 1);
        assert(wbif.wb_out.s_rw == 5'h4);  // Load takes priority
        assert(wbif.wb_out.s_wdata == 32'hFEEDFADE);

        // Test Case 4: No writeback
        wbif.alu_ready = 0;
        wbif.load_ready = 0;
        #10;
        assert(wbif.wb_out.s_rw_en == 0);

        // End simulation
        #20;
        $display("All tests passed!");
        $stop;
    end
endmodule

