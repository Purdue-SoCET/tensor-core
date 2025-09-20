/*
    Timing Control testbench
*/

`include "dram_pkg.vh"
`include "timing_signals_if.vh"
`include "command_fsm_if.vh"

`timescale 1 ns / 1 ns

module timing_control_tb ();
    
    // import packages
    import dram_pkg::*;

    parameter PERIOD = 10;
    parameter INDEX_BITS = 11;

    logic tb_CLK = 0, tb_nRST;

    // clock
    always #(PERIOD/2) tb_CLK++;

    //*****************************************************************************
    // Declare DUT Signals
    //*****************************************************************************
    timing_signals_if tb_timif ();
    command_fsm_if    tb_cfsmif ();

    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    `ifndef MAPPED
        timing_control DUT (.clk(tb_CLK), .nRST(tb_nRST), .timif(tb_timif), .cfsmif(tb_cfsmif));
    `else
        addr_mapper DUT (
            .\clk                   (tb_CLK),
            .\nRST                  (tb_nRST),
            .\timif.tACT_done       (tb_timif.tACT_done),
            .\timif.tWR_done        (tb_timif.tWR_done),
            .\timif.tRD_done        (tb_timif.tRD_done),
            .\timif.tPRE_done       (tb_timif.tPRE_done),
            .\timif.tREF_done       (tb_timif.tREF_done),
            .\timif.rf_req          (tb_timif.rf_req),
            .\cfsmif.cmd_state      (tb_cfsmif.cmd_state),       
        );
    `endif

    //*****************************************************************************
    // Declare TB Signals
    //*****************************************************************************
    string   tb_test_case;
    integer  tb_test_case_num;
    integer  tb_i;
    logic    tb_mismatch;
    logic    tb_check;

    // expected value signals
    timing_signals_if tb_expected_timif  ();

    //*****************************************************************************
    // Declare TB tasks
    //*****************************************************************************
    task reset_dut;
        begin
            // Activate the reset
            tb_nRST = 1'b0;

            // Maintain the reset for more than one cycle
            @(posedge tb_CLK);
            @(posedge tb_CLK);

            // Wait until safely away from rising edge of the clock before releasing
            @(negedge tb_CLK);
            tb_nRST = 1'b1;

            // Leave out of reset for a couple cycles before allowing other stimulus
            // Wait for negative clock edges, 
            // since inputs to DUT should normally be applied away from rising clock edges
            @(negedge tb_CLK);
            @(negedge tb_CLK);
        end
    endtask

    task check_output;
        begin
            tb_mismatch = 1'b0;
            tb_check    = 1'b1;
            
            if (tb_expected_timif.tACT_done == tb_timif.tACT_done) begin
                $display("Correct 'tACT_done' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect '' output during %s test case", tb_test_case);
            end

            if (tb_expected_timif.tWR_done == tb_timif.tWR_done) begin
                $display("Correct 'tWR_done' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'tWR_done' output during %s test case", tb_test_case);
            end

            if (tb_expected_timif.tRD_done == tb_timif.tRD_done) begin
                $display("Correct 'tRD_done' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect '' output during %s test case", tb_test_case);
            end

            if (tb_expected_timif.tPRE_done == tb_timif.tPRE_done) begin
                $display("Correct 'tPRE_done' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'tPRE_done' output during %s test case", tb_test_case);
            end

            if (tb_expected_timif.tREF_done == tb_timif.tREF_done) begin
                $display("Correct 'tREF_done' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'tREF_done' output during %s test case", tb_test_case);
            end

            // if (tb_expected_timif.rf_req == tb_timif. rf_req) begin
            //     $display("Correct 'rf_req' output during %s test case", tb_test_case);
            // end
            // else begin
            //     tb_mismatch = 1'b1;
            //     $display("Incorrect 'rf_req' output during %s test case", tb_test_case);
            // end

            // Wait some small amount of time so check pulse timing is visible on waves
            #(0.1);
            tb_check = 1'b0;
        end
    endtask

    task check_refresh;
        begin
            tb_mismatch = 1'b0;
            tb_check    = 1'b1;
        
            if (tb_expected_timif.rf_req == tb_timif. rf_req) begin
                $display("Correct 'rf_req' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'rf_req' output during %s test case", tb_test_case);
            end

            // Wait some small amount of time so check pulse timing is visible on waves
            #(0.1);
            tb_check = 1'b0;
        end
    endtask

    //*****************************************************************************
    //*****************************************************************************
    // Main TB Process
    //*****************************************************************************
    //*****************************************************************************
    initial begin
        
        // Initialize Test Case Navigation Signals
        tb_test_case       = "Initilization";
        tb_test_case_num   = 0;
        tb_check           = 1'b0;
        tb_mismatch        = 1'b0;
        tb_i               = '0;

        // Initialize DUT signals
        tb_cfsmif.cmd_state = IDLE;
    
        //*****************************************************************************
        // Power-on-Reset Test Case
        //*****************************************************************************
        tb_test_case     = "Power-on-Reset";
        tb_test_case_num = tb_test_case_num + 1;

        reset_dut();
        
        tb_expected_timif.tACT_done = 1'b0;      
        tb_expected_timif.tWR_done  = 1'b0;         
        tb_expected_timif.tRD_done  = 1'b0;          
        tb_expected_timif.tPRE_done = 1'b0;         
        tb_expected_timif.tREF_done = 1'b0;         
        tb_expected_timif.rf_req    = 1'b0;   

        @(posedge tb_CLK)
        check_output();

        #(tb_CLK * 3);

        //*****************************************************************************
        // ACT -> RD/WRITE
        //*****************************************************************************
        tb_test_case     = "ACT -> RD/WRITE";
        tb_test_case_num = tb_test_case_num + 1;

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = ACTIVATE;     // time loaded, counter enabled   

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = ACTIVATING;                    // state changed after pos edge
        repeat (tRCD - tAL - 1) @(posedge tb_CLK);           // waiting for timer to finish counting

        @(negedge tb_CLK)
        tb_expected_timif.tACT_done = 1'b1; // timer should finish counting
        check_output();

        @(posedge tb_CLK)
        tb_expected_timif.tACT_done = 1'b0; // clearing expected value signal

        #(tb_CLK * 3);

        //*****************************************************************************
        // READ
        //*****************************************************************************
        tb_test_case     = "READ";
        tb_test_case_num = tb_test_case_num + 1;

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = READ;     // time loaded, counter enabled   

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = READING;                   // state changed after pos edge
        repeat (tRL + tBURST - 1) @(posedge tb_CLK);           // waiting for timer to finish counting

        @(negedge tb_CLK)
        tb_expected_timif.tRD_done = 1'b1; // timer should finish counting
        check_output();

        @(posedge tb_CLK)
        tb_expected_timif.tRD_done = 1'b0; // clearing expected value signal

        #(tb_CLK * 3);

        //*****************************************************************************
        // Write
        //*****************************************************************************
        tb_test_case     = "WRITE";
        tb_test_case_num = tb_test_case_num + 1;

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = WRITE;     // time loaded, counter enabled   

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = WRITING;            // state changed after pos edge
        repeat (tWL - 1) @(posedge tb_CLK);           // wr_en should go high
        repeat (tBURST) @(posedge tb_CLK);        // waiting for timer to finish counting

        @(negedge tb_CLK)
        tb_expected_timif.tWR_done = 1'b1; // timer should finish counting
        check_output();

        @(posedge tb_CLK)
        tb_expected_timif.tWR_done = 1'b0; // clearing expected value signal

        #(tb_CLK * 3);

        //*****************************************************************************
        // PRECHARGE
        //*****************************************************************************
        tb_test_case     = "PRECHARGE";
        tb_test_case_num = tb_test_case_num + 1;

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = PRECHARGE;        // time loaded, counter enabled

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = PRECHARGING;      // state changed after pos edge   

        repeat (tRP - 1) @(posedge tb_CLK);     // waiting for timer to finish counting

        @(negedge tb_CLK)
        tb_expected_timif.tPRE_done = 1'b1;     // timer should finish counting
        check_output();

        @(posedge tb_CLK)
        tb_expected_timif.tPRE_done = 1'b0;      // clearing expected value signal

        #(tb_CLK * 3);

        //*****************************************************************************
        // REFRESH
        //*****************************************************************************
        tb_test_case     = "REFRESH";
        tb_test_case_num = tb_test_case_num + 1;

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = REFRESH;           // time loaded, counter enabled

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = REFRESHING;                   // state changed after pos edge

        repeat (tRFC - 1) @(posedge tb_CLK);         // waiting for timer to finish counting

        @(negedge tb_CLK)
        tb_expected_timif.tREF_done = 1'b1;      // timer should finish counting
        check_output();

        @(posedge tb_CLK)
        tb_expected_timif.tREF_done = 1'b0;      // clearing expected value signal

        #(tb_CLK * 3);

        //*****************************************************************************
        // REFRESH Request
        //*****************************************************************************
        tb_test_case     = "Refresh request";
        tb_test_case_num = tb_test_case_num + 1;

        @(posedge tb_CLK)                       
        tb_cfsmif.cmd_state = IDLE;

        reset_dut();                            // to reset refresh counter
        
        repeat (tREFI - 2) @(posedge tb_CLK);    // waiting for refresh counter to reach tREFI

        @(negedge tb_CLK)
        tb_expected_timif.rf_req = 1'b1;      // refresh timer should finish counting
        check_refresh();

        // At this point, refresh request is not serviced.
        // Refresh counter should keep increasing
        repeat (20) @(posedge tb_CLK);        // refresh_count = tREFI + 20

        @(posedge tb_CLK)
        tb_cfsmif.cmd_state = REFRESH;
        
        @(negedge tb_CLK)                       
        tb_expected_timif.rf_req= 1'b0;      // Refresh request is now satisfied. clearing expected value signal
        check_refresh();

        #(tb_CLK * 3);

        $finish;

    end
endmodule