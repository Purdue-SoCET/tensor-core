`timescale 1ps/1ps

`include "dram_top_if.vh"

module dram_top_tb ();
    import dram_pkg::*;
    logic CLK, nRST;
    localparam CLK_PERIOD = 1250;
    string test_case;

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

    initial begin
        reset_cmd();

        $finish;
    end


endmodule