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
    timing_signals_if   tb_timif ();

    assign tb_polif.row_resolve  = tb_cfsmif.row_resolve;
    assign tb_cfsmif.init_done   = tb_initif.init_valid;
    assign tb_initif.init        = tb_cfsmif.init_req;
    assign tb_polif.req_en       = tb_cfsmif.dREN || tb_cfsmif.dWEN;

    assign tb_amif.configs = x8;

    
    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    init_addr_row_cmd DUT (.clk(tb_CLK), .nRST(tb_nRST), .amif(tb_amif), .initif(tb_initif),
                           .polif(tb_polif), .cfsmif(tb_cfsmif), .timif(tb_timif));

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
    row_open_if    tb_expected_polif  ();

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
        repeat (tPWUP*3 + tPDc + tXPR + tDLLKc + tMOD*7 + tZQinitc) @(posedge tb_CLK);
    endtask

    task check_init;
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

            #(tb_CLK * 3);
            tb_check    = 1'b0;
        end
    endtask

    task check_row;
        begin
            tb_mismatch = 1'b0;
            tb_check    = 1'b1;

            if (tb_expected_polif.row_stat == tb_polif.row_stat) begin
                $display("Correct 'row status' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'row_status' output during %s test case", tb_test_case);
            end

            if (tb_expected_cfsmif.cmd_state == tb_cfsmif.cmd_state) begin
                $display("Correct 'cmd_state' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'cmd_state' output during %s test case", tb_test_case);
            end

            #(tb_CLK * 3);
            tb_check    = 1'b0;
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
        // cfsm signals
        tb_cfsmif.dREN              = 1'b0;
        tb_cfsmif.dWEN              = 1'b0;
        
        // timing signals
        tb_timif.rf_req            = 1'b0;
        tb_timif.tACT_done         = 1'b0;
        tb_timif.tWR_done          = 1'b0;
        tb_timif.tRD_done          = 1'b0;
        tb_timif.tPRE_done         = 1'b0;
        tb_timif.tREF_done         = 1'b0;

        // address mapper signals
        tb_amif.address             = '0;

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
        check_init();

        #(tb_CLK * 3);
        
        @(posedge tb_CLK)

        //*****************************************************************************
        // Row miss interaction
        //*****************************************************************************
        tb_test_case     = "Row miss interaction";
        tb_test_case_num = tb_test_case_num + 1;

        // Set a read request to address all 0s to activate a row
        @(negedge tb_CLK)
        tb_cfsmif.dREN              = 1'b1;      //
        tb_amif.address             = '0;
        // tb_amif.BG                  = '0;
        // tb_amif.bank                = '0;
        // tb_amif.row                 = '0;

        //@(posedge tb_CLK)           // row open policy should see the row miss now

        //@(negedge tb_CLK)
        tb_expected_polif.row_stat = 2'b10; // row status should be MISS (2'b10)
        check_row();

        // continue activating the row
        @(posedge tb_CLK)
        
        @(negedge tb_CLK)
        tb_expected_polif.row_stat = 2'b01; // row status should be HIT (2'b01) because status table updated
        tb_expected_cfsmif.cmd_state = ACTIVATE;
        check_row();

        @(posedge tb_CLK)               // cmd_state should now be ACTIVATING
        
        @(negedge tb_CLK)
        tb_timif.tACT_done = 1'b1;        // setting the ACT_done high
        tb_expected_cfsmif.cmd_state = ACTIVATING;
        check_row();

        @(posedge tb_CLK)               // cmd_state should now be READ
        
        @(negedge tb_CLK)
        tb_timif.tACT_done = 1'b0;        // setting the ACT_done low
        tb_expected_cfsmif.cmd_state = READ;
        check_row();

        @(posedge tb_CLK)               // cmd_state should now be READING

        @(negedge tb_CLK)
        tb_timif.tRD_done = 1'b1;        // setting the RD_done high
        tb_expected_cfsmif.cmd_state = READING;
        tb_cfsmif.dREN = 1'b0;
        check_row();

        @(posedge tb_CLK)               // cmd_state should now be IDLE
        
        @(negedge tb_CLK)
        tb_timif.tRD_done = 1'b0;        // setting the RD_done high
        tb_expected_cfsmif.cmd_state = IDLE;
        tb_expected_polif.row_stat = 2'b01;         // WHY IS THE DEFAULT 0?
        check_row();

        #(tb_CLK * 3);

        @(posedge tb_CLK)

        //*****************************************************************************
        // Row hit interaction
        //*****************************************************************************
        tb_test_case     = "Row hit interaction";
        tb_test_case_num = tb_test_case_num + 1;

        @(negedge tb_CLK)
        tb_cfsmif.dWEN = 1'b1;

        //@(posedge tb_CLK)           // row open policy should see the row hit now

        //@(negedge tb_CLK)
        tb_expected_polif.row_stat = 2'b01;  // row status should be HIT (2'b01)
        check_row();

        @(posedge tb_CLK)           // cmd_state should now be WRITE
        
        @(negedge tb_CLK)
        tb_expected_cfsmif.cmd_state = WRITE;
        check_row();

        @(posedge tb_CLK)               // cmd_state should now be WRITING

        @(negedge tb_CLK)
        tb_timif.tWR_done = 1'b1;        // setting the WR_done high
        tb_expected_cfsmif.cmd_state = WRITING;
        tb_cfsmif.dWEN = 1'b0;
        check_row();

        @(posedge tb_CLK)               // cmd_state should now be IDLE
        
        @(negedge tb_CLK)
        tb_timif.tWR_done = 1'b0;        // setting the RD_done high
        tb_expected_cfsmif.cmd_state = IDLE;
        tb_expected_polif.row_stat = 2'b01;         //
        check_row();

        #(tb_CLK * 3);

        @(posedge tb_CLK)

        //*****************************************************************************
        // Row conflict interaction
        //*****************************************************************************
        tb_test_case     = "Row conflict interaction";
        tb_test_case_num = tb_test_case_num + 1;

        @(negedge tb_CLK)
        tb_amif.address[30:16] = 15'h1;         // same BG and bank but diff row. Should be row conflict
        tb_expected_polif.row_stat = 2'b11;

        #(tb_CLK * 3);

        @(posedge tb_CLK)
        


    end

endmodule