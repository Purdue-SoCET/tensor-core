/*
    This testbench tests the Init FSM, Addr Mapper, Row Policy, and Cmd FSM modules
    of the control unit.
    The main interactions checked are:
    1. 
*/

`include "dram_pkg.vh"
`include "address_mapper_if.vh"
`include "timing_signals_if.vh"
`include "command_fsm_if.vh"
`include "row_open_if.vh"
`include "init_state_if.vh"

`timescale 1 ns / 1 ns

module init_addr_row_cmd_tb ();
    
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
    command_fsm_if      tb_cfsmif ();
    address_mapper_if   tb_amif ();
    row_open_if         tb_polif ();
    init_state_if       tb_initif ();

    assign tb_polif.row_resolve  = tb_cfsmif.row_resolve;
    assign tb_cfsmif.init_done   = tb_initif.init_valid;
    assign tb_initif.init        = tb_cfsmif.init_req;

    
    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    init_addr_row_cmd DUT (.clk(tb_CLK), .nRST(tb_nRST), .amif(tb_amif), .initif(tb_initif),
                           .polif(tb_polif), .cfsmif(tb_cfsmif));

    //*****************************************************************************
    // Declare TB Signals
    //*****************************************************************************
    string   tb_test_case;
    integer  tb_test_case_num;
    integer  tb_i;
    logic    tb_mismatch;
    logic    tb_check;

    // expected value signals
    init_state_if  tb_expected_initif ();
    command_fsm_if tb_expected_cfsmif ();

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

    task wait_for_initialization;
        repeat (tRESET + tPWUP + tRESETCKE + tPDc + tXPR + tDLLKc + tMOD * 7 + tZQinitc) @(posedge tb_CLK);
    endtask

    task check_output;
        begin
            tb_mismatch = 1'b0;
            tb_check    = 1'b1;

            if (tb_expected_initif.init_valid == tb_initif.init_valid) begin
                $display("Correct 'init_valid' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'init_valid' output during %s test case", tb_test_case);
            end

            if (tb_expected_cfsmif.cmd_state == tb_cfsmif.cmd_state) begin
                $display("Correct 'cmd_state' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'cmd_state' output during %s test case", tb_test_case);
            end
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
        tb_cfsmif.dREN     = 1'b0;
        tb_cfsmif.dWEN     = 1'b0;
        tb_cfsmif.tACT_done         = 1'b0;
        tb_cfsmif.tWR_done         = 1'b0;
        tb_cfsmif.tRD_done         = 1'b0;
        tb_cfsmif.tPRE_done         = 1'b0;
        tb_cfsmif.tREF_done         = 1'b0;

        //*****************************************************************************
        // Power-on-Reset Test Case
        //*****************************************************************************
        tb_test_case     = "Power-on-Reset";
        tb_test_case_num = tb_test_case_num + 1;

        reset_dut();

        #(tb_CLK * 3);

        //*****************************************************************************
        // Init done check
        //*****************************************************************************
        tb_test_case     = "Init done check";
        tb_test_case_num = tb_test_case_num + 1;

        // wait for initialization to complete
        wait_for_initialization();

        // init done should be high, cmd fsm should go to idle
        @(negedge tb_CLK)
        tb_expected_initif.init_valid = 1'b1;
        tb_expected_cfsmif.cmd_state  = IDLE;
        check_output();

        #(tb_CLK * 3);
    end

endmodule