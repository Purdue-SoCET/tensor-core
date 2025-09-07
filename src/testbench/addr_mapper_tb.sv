/*
    Address Mapper testbench
*/

`include "address_mapper_if.vh"
`include "dram_pkg.vh"

`timescale 1 ns / 1 ns

module addr_mapper_tb ();
    
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
    address_mapper_if tb_amif ();

    //*****************************************************************************
    // DUT Instance
    //*****************************************************************************
    `ifndef MAPPED
        addr_mapper DUT (.amif(tb_amif));
    `else
        addr_mapper DUT (
            .\amif.address          (tb_amif.address),
            .\amif.configs          (tb_amif.configs),
            .\amif.rank             (tb_amif.rank),
            .\amif.BG               (tb_amif.BG),
            .\amif.bank             (tb_amif.bank),
            .\amif.row              (tb_amif.row),
            .\amif.col              (tb_amif.col),
            .\amif.offset           (tb_amif.offset),
            .\amif.ignore           (tb_amif.ignore)
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
    address_mapper_if tb_expected_amif ();

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
            
            if (tb_expected_amif.rank == tb_amif.rank) begin
                $display("Correct 'rank' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'rank' output during %s test case", tb_test_case);
            end

            if (tb_expected_amif.BG == tb_amif.BG) begin
                $display("Correct 'BG' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'BG' output during %s test case", tb_test_case);
            end

            if (tb_expected_amif.bank == tb_amif.bank) begin
                $display("Correct 'bank' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'bank' output during %s test case", tb_test_case);
            end

            if (tb_expected_amif.row == tb_amif.row) begin
                $display("Correct 'row' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'row' output during %s test case", tb_test_case);
            end

            if (tb_expected_amif.col == tb_amif.col) begin
                $display("Correct 'col' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'col' output during %s test case", tb_test_case);
            end

            if (tb_expected_amif.offset == tb_amif.offset) begin
                $display("Correct 'offset' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'offset' output during %s test case", tb_test_case);
            end

            if (tb_expected_amif.ignore == tb_amif.ignore) begin
                $display("Correct 'ignore' output during %s test case", tb_test_case);
            end
            else begin
                tb_mismatch = 1'b1;
                $display("Incorrect 'ignore' output during %s test case", tb_test_case);
            end

            // Wait some small amount of time so check pulse timing is visible on waves
            #(0.1);
            tb_check =1'b0;
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
        tb_amif.address = '0;
        tb_amif.configs = '0;
    
        //*****************************************************************************
        // Power-on-Reset Test Case (Not needed because combinational. USING AS A RESET)
        //*****************************************************************************
        tb_test_case     = "Power-on-Reset";
        tb_test_case_num = tb_test_case_num + 1;

        reset_dut();
        
        //tb_expected_   = '0;

        @(posedge tb_CLK)
        //check_output();

        #(tb_CLK * 3);

        //*****************************************************************************
        // 0xFFFFFFFF, x4
        //*****************************************************************************
        tb_test_case     = "Config = x4, Address = 0xFFFFFFFF";
        tb_test_case_num = tb_test_case_num + 1;

        @(negedge tb_CLK)
        tb_amif.address = 32'hFFFFFFFF;
        tb_amif.configs = x4;

        tb_expected_amif = 32'hFFFFFFFF;

        @(posedge tb_CLK)
        check_output();

        #(tb_CLK * 3);



    end
endmodule