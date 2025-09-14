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
                $display("Incorrect '' output during %s test case", tb_test_case);
            end

            if (tb_expected_timif.tREF_done == tb_timif.tREF_done) begin
                $display("Correct 'tREF_done' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'tREF_done' output during %s test case", tb_test_case);
            end

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
        // Power-on-Reset Test Case (Not needed because combinational. USING AS A RESET)
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
        // Add more test cases
        //*****************************************************************************

        $finish;

    end
endmodule