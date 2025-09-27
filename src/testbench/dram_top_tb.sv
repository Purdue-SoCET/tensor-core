`timescale 1ps/1ps

`include "dram_top_if.vh"


module dram_top_tb ();
    import dram_pkg::*;
    logic CLK, nRST;
    localparam CLK_PERIOD = 1250;
    string test_case;

    
    localparam logic        RANK0      = 1'b0;
    localparam logic [13:0] ROW_HIT    = 14'h1234;   // "open" row for the hit/conflict cases
    localparam logic [13:0] ROW_OTHER  = 14'h2ACE;   // different row -> conflict
    localparam logic [1:0]  BANK1      = 2'b01;
    localparam logic [1:0]  BANK2      = 2'b10;      // different bank -> miss (assuming closed)
    localparam logic        BG1        = 1'b1;
    localparam logic        BG0        = 1'b0;
    localparam logic [9:0]  COL_A      = 10'b0001100011; // same row, different columns = hit
    localparam logic [9:0]  COL_B      = 10'b0010010100;
    localparam logic [2:0]  OFFS0      = 3'b000;


    function automatic logic [31:0] pack_addr(
        input logic        rank,
        input logic [13:0] row,
        input logic [1:0]  bank,
        input logic        bg1,
        input logic [9:0]  col,
        input logic        bg0,
        input logic [2:0]  offs
    );
        pack_addr = {
            rank,
            row,
            bank,
            bg1,
            col[9:3],
            bg0,
            col[2:0],
            offs
        };
    endfunction

    // -------------------------- ROW HIT ----------------------------------
    // Same {rank, bank, BG, row}; different columns (COL_A vs COL_B)
    localparam logic [31:0] ADDR_HIT_A = pack_addr(RANK0, ROW_HIT, BANK1, BG1, COL_A, BG0, OFFS0);
    localparam logic [31:0] ADDR_HIT_B = pack_addr(RANK0, ROW_HIT, BANK1, BG1, COL_B, BG0, OFFS0);
    // ------------------------ ROW CONFLICT -------------------------------
    // Same {rank, bank, BG}, but different row -> requires PRECHARGE then ACTIVATE
    localparam logic [31:0] ADDR_CONFLICT = pack_addr(RANK0, ROW_OTHER, BANK1, BG1, COL_A, BG0, OFFS0);
    // -------------------------- ROW MISS ---------------------------------
    // Different bank (or BG/rank) that has no row open -> ACTIVATE only (no precharge)
    localparam logic [31:0] ADDR_MISS = pack_addr(RANK0, ROW_HIT, BANK2, BG1, COL_A, BG0, OFFS0);

    dram_top_if mycmd();
    // Clock Generator
    always begin
        CLK = 1'b0;
        #(CLK_PERIOD / 2.0);
        CLK = 1'b1;
        #(CLK_PERIOD / 2.0);
    end
    

    dram_top DUT (
        .CLK(CLK),
        .nRST(nRST),
        .mytop(mycmd),
        .mycsm(mycmd)
    );


    task reset_cmd();
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
        mycmd.ram_addr = 0;
        mycmd.ramstore = 0;

        repeat(2) @(posedge CLK);
        nRST = 1'b1;
        @(posedge CLK);

    endtask

    task initialization();
        #((tRESET + tPWUP + tRESETCKE + tPDc + tXPR + tDLLKc + tMOD * 7 + tZQinitc) * CLK_PERIOD);
        repeat(25) @(posedge CLK); //Adding more 11 cycles?
    endtask

    // Task to drive a request for one cycle
    task drive_req (
        input logic is_write, 
        input logic [31:0] addr
    );
        mycmd.dWEN = is_write;
        mycmd.dREN = !is_write;
        mycmd.ram_addr = addr;
        @(posedge CLK);
    endtask

    // TEST 1: Write Miss (IDLE -> ACTIVATE -> ACTIVATING -> WRITE -> WRITING -> IDLE)
    task test_write_miss;
        $display("[INFO] Running Test Case: %s", test_case);
        
        drive_req(1, 32'hAAAA_AAAA); // is_write=1, stat=MISS
        @(posedge CLK);
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
        mycmd.ram_addr = 32'h0;
        @(posedge CLK);
        mycmd.tWR_done = 0;
    endtask

    // TEST 2: Read Miss (IDLE -> ACTIVATE -> ACTIVATING -> READ -> READING -> IDLE)
    task test_read_miss;
        $display("[INFO] Running Test Case: %s", test_case);
        drive_req(0, ADDR_MISS); // is_write=0, stat=MISS
        @(posedge CLK);
        @(posedge CLK);
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        @(posedge CLK);
        mycmd.tRD_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.ram_addr = 00;
        @(posedge CLK);
        mycmd.tRD_done = 0;
        @(posedge CLK);
    endtask

    // TEST 3: Row Hit (IDLE -> WRITE -> WRITING -> READ -> READING -> IDLE)
    task test_write_hit;
        $display("[INFO] Running Test Case: %s", test_case);
        drive_req(1, 32'hAAAA_AAAA); // is_write=1, stat=MISS
        @(posedge CLK);
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
        mycmd.ram_addr = 32'h0;
        @(posedge CLK);
        mycmd.tWR_done = 0;
    endtask

    // TEST 4: Row Hit (IDLE -> WRITE -> WRITING -> READ -> READING -> IDLE)
    task test_read_hit;
        $display("[INFO] Running Test Case: %s", test_case);
        drive_req(0, 32'hAAAA_AAAA); // is_write=1, stat=MISS
        @(posedge CLK);
        @(posedge CLK);
        // Signal tACT_done, should move to WRITE
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        // Next state should be WRITING
        @(posedge CLK);
    
        // Signal tWR_done, should return to IDLE as there are no pending requests
        mycmd.tRD_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.ram_addr = 32'h0;
        @(posedge CLK);
        mycmd.tRD_done = 0;
    endtask

    //TEST 5:
    task test_conflict();
        drive_req(1, ADDR_HIT_A); // is_write=1, stat=MISS
        @(posedge CLK);
        @(posedge CLK);
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        @(posedge CLK);
        mycmd.tWR_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.ram_addr = 32'h0;
        @(posedge CLK);
        mycmd.tWR_done = 0;

        @(posedge CLK);
        drive_req(0, ADDR_CONFLICT); // is_write=1, stat=MISS
        @(posedge CLK);
        @(posedge CLK);
        mycmd.tPRE_done = 1;
        @(posedge CLK);
        mycmd.tPRE_done = 0;
        repeat(4) @(posedge CLK);
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        @(posedge CLK);
        mycmd.tRD_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.ram_addr = 32'h0;
        @(posedge CLK);
        mycmd.tRD_done = 0;
        repeat (4) @(posedge CLK);
    endtask

    
    task test_read_but_refresh;
        $display("[INFO] Running Test Case: %s", test_case);
        drive_req(0, 32'hAAAA_AAAA); // is_write=1, stat=MISS
        @(posedge CLK);
        
        // Signal tACT_done, should move to READ
        mycmd.rf_req = 1;
        repeat (15) @(posedge CLK);
        
        mycmd.tREF_done = 1;
        @(posedge CLK);
        mycmd.tREF_done = 0;

        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        // Next state should be READING
        @(posedge CLK);
        
        
        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);
        // Signal tACT_done, should move to READ
        mycmd.tACT_done = 1;
        @(posedge CLK);
        mycmd.tACT_done = 0;
        // Next state should be READING
        // Signal tWR_done, should return to IDLE as there are no pending requests
        mycmd.tRD_done = 1;
        mycmd.dWEN = 0;
        mycmd.dREN = 0;
        mycmd.ram_addr = 32'h0;
        @(posedge CLK);
        mycmd.tRD_done = 0;
    endtask



    initial begin
        test_case = "reset_cmd";
        reset_cmd();
        test_case = "initialization";
        initialization();
        test_case = "test_write_miss";
        test_write_miss();
        test_case = "test_read_miss";
        test_read_miss();
        test_case = "test_write_hit";
        test_write_hit();
        test_case = "test_read_hit";
        test_read_hit();
        test_case = "test_conflict";
        test_conflict();

        test_case = "test_read_but_refresh";
        test_read_but_refresh();
        $finish;
    end


endmodule