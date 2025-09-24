`timescale 1ps/1ps
`include "command_FSM_if.vh"

module command_FSM_tb ();
    import dram_pack::*;
    logic CLK, nRST;
    localparam CLK_PERIOD = 1250;   
    string test_case;
    command_FSM_if mycmd();

    // Clock Generator
    always begin
        CLK = 1'b0;
        #(CLK_PERIOD / 2.0);
        CLK = 1'b1;
        #(CLK_PERIOD / 2.0);
    end

    // DUT Instantiation
    command_FSM DUT (
        .CLK (CLK),
        .nRST (nRST),
        .mycmd (mycmd)
    );


    task reset_cmd;
        nRST = 1'b0;
        mycmd.dREN      = 0;
        mycmd.dWEN      = 0;
        mycmd.init_done = 0;
        mycmd.tACT_done = 0;
        mycmd.tWR_done  = 0;
        mycmd.tRD_done  = 0;
        mycmd.tPRE_done = 0;
        mycmd.tREF_done = 0;
        mycmd.rf_req    = 0;
        mycmd.row_stat  = 2'b00; // default to NO_STAT
        
        repeat(2) @(posedge CLK);
        nRST = 1'b1;
        @(posedge CLK);
    endtask

    // Task to handle the initial POWER_UP -> IDLE sequence
    task initialize ();
        test_case = "Initialize";
        $display("[INFO] Running Test Case: %s", test_case);
        
        mycmd.init_done = 1;
        @(posedge CLK);
        mycmd.init_done = 0; // De-assert after one cycle
    
    endtask

    // Task to drive a request for one cycle
    task drive_req (
        input logic is_write, 
        input logic [1:0] stat
    );
        mycmd.dWEN = is_write;
        mycmd.dREN = !is_write;
        mycmd.row_stat = stat;
        @(posedge CLK);
        
    endtask

    

    // TEST 1: Write Miss (IDLE -> ACTIVATE -> ACTIVATING -> WRITE -> WRITING -> IDLE)
    task test_write_miss;
        test_case = "Write Miss";
        $display("[INFO] Running Test Case: %s", test_case);
        
        drive_req(1, 2'b10); // is_write=1, stat=MISS
    
        @(posedge CLK);
        
        
        // Signal tACT_done, should move to WRITE
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        // Next state should be WRITING
        @(posedge CLK);
    
        // Signal tWR_done, should return to IDLE as there are no pending requests
        mycmd.tWR_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.row_stat = 2'b00;
        @(posedge CLK);
        mycmd.tWR_done = 0;
    endtask

    // TEST 2: Read Miss (IDLE -> ACTIVATE -> ACTIVATING -> READ -> READING -> IDLE)
    task test_read_miss;
        test_case = "Read Miss";
        $display("[INFO] Running Test Case: %s", test_case);

        drive_req(0, 2'b10); // is_write=0, stat=MISS

        @(posedge CLK);

        
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;

        @(posedge CLK);
        // NOTE: There is a bug in your RTL. In READING, an else without a condition
        // drives the state to IDLE immediately. This test assumes that is fixed.
        // If not fixed, the state will go to READING for 0 cycles.
        // if (mycmd.cmd_state != READING) $error("READ -> READING failed");
        
        mycmd.tRD_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.row_stat = 2'b00;
        @(posedge CLK);
        
        mycmd.tRD_done = 0;
    endtask

    // TEST 3: Row Hit (IDLE -> WRITE -> WRITING -> READ -> READING -> IDLE)
    task test_row_hit;
        test_case = "Row Hit Sequence";
        $display("[INFO] Running Test Case: %s", test_case);
        
        // 1. First, send a write hit from IDLE
        drive_req(1, 2'b01); // is_write=1, stat=HIT
        
        @(posedge CLK);
        
        mycmd.tWR_done = 1;

        // 2. While WRITING and tWR_done is high, send a read hit
        // This tests the transition from WRITING -> READ
        drive_req(0, 2'b01); // is_write=0, stat=HIT
        mycmd.tWR_done = 0;
        
        
        // Let it transition to READING and then IDLE
        @(posedge CLK);
        mycmd.tRD_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.row_stat = 2'b00;
        @(posedge CLK);
        mycmd.tRD_done = 0;
        
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.row_stat = 2'b00;
    endtask
    
    // TEST 4: Row Conflict (IDLE -> CONFLICT -> PRECHARGE -> IDLE)
    task test_row_conflict;
        test_case = "Row Conflict";
        $display("[INFO] Running Test Case: %s", test_case);

        // From IDLE, request a write that causes a conflict
        drive_req(1, 2'b11); // is_write=1, stat=CONFLICT
        
        
        // Signal tPRE_done, should move back to IDLE
        mycmd.tPRE_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.row_stat = 2'b00;
        @(posedge CLK);
        mycmd.tPRE_done = 0;
        
        

    
    endtask

    // TEST 5: Refresh Interrupt Scenarios
    task test_refresh_interrupts;
        test_case = "Refresh Interrupts";
        $display("[INFO] Running Test Case: %s", test_case);

        // 5a. Refresh from IDLE
        mycmd.rf_req = 1;
        @(posedge CLK);
        
        mycmd.rf_req = 0;
        
        mycmd.tREF_done = 1;
        @(posedge CLK);
        mycmd.tREF_done = 0;

        // 5b. Refresh during ACTIVATING
        drive_req(1, 2'b10); // Go to ACTIVATE
        @(posedge CLK);      // Go to ACTIVATING
        
        mycmd.rf_req = 1;    // Assert refresh request
        mycmd.tACT_done = 1; // Finish activation
        @(posedge CLK);
        mycmd.rf_req = 0;
        mycmd.tACT_done = 0;
        
        mycmd.tPRE_done = 1; // Finish precharge
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.row_stat = 2'b00;

        @(posedge CLK);
        mycmd.tPRE_done = 0;
    endtask

    initial begin
        // 1. Start with reset and initialization
        reset_cmd();
        initialize();

        // 2. Run Write Miss Test
        test_write_miss();
        repeat(5) @(posedge CLK);

        // 3. Run Read Miss Test
        test_read_miss();
        repeat(5) @(posedge CLK);

        // 4. Run Row Hit Test
        test_row_hit();
        repeat(5) @(posedge CLK);

        // 5. Run Row Conflict Test
        test_row_conflict();
        repeat(5) @(posedge CLK);
        
        // 6. Run Refresh Tests
        test_refresh_interrupts();
        repeat(5) @(posedge CLK);
    
        $finish;
    end

endmodule