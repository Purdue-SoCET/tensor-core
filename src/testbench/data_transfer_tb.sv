`timescale 1ns / 1ps
`include "data_transfer_if.vh"
`include "dram_command_if.vh"

module data_transfer_tb();
    import dram_pack::*;
    localparam CLK_PERIOD = 1.5;
    // localparam CLK_PERIOD = 1.25;
    logic CLK, CLKx2;
    logic nRST;
    logic [CONFIGURED_DQ_BITS - 1:0] DQ_tb;
    logic [CONFIGURED_DQS_BITS - 1 :0] DQS_t_tb, DQS_c_tb;

    data_transfer_if dtif();

    data_transfer DUT (
        .CLK(CLK),
        .CLKx2(CLKx2),
        .nRST(nRST),
        .mydata(dtif)
    );

    always begin
        CLK = 1'b0;
        #(CLK_PERIOD / 2.0);
        CLK = 1'b1;
        #(CLK_PERIOD / 2.0);
    end

    always begin
        CLKx2 = 1'b1;
        #(CLK_PERIOD / 4.0);
        CLKx2 = 1'b0;
        #(CLK_PERIOD / 4.0);
    end

    assign dtif.DQ    = (dtif.rd_en) ? DQ_tb : 'z;
    assign dtif.DQS_t = (dtif.rd_en) ? DQS_t_tb:  'z;
    assign dtif.DQS_c = (dtif.rd_en) ? ~DQS_t_tb:   'z; 

    task write (
        input logic [31:0] data_store1,
        input logic [31:0] data_store2,
        input logic [31:0] data_store3,
        input logic [31:0] data_store4,
        input logic [2:0] COL_choice
    );
        dtif.COL_choice = COL_choice;
        dtif.wr_en = 1'b1;
        dtif.memstore = data_store1;
        repeat (2) @(posedge CLKx2);
        @(posedge CLKx2);
        dtif.memstore = data_store1;
        @(posedge CLKx2);
        dtif.memstore = data_store2;
        @(posedge CLKx2);
        dtif.memstore = data_store3;
        @(posedge CLKx2);
        dtif.memstore = data_store4;
        @(posedge CLKx2);
        dtif.memstore = data_store1;
        @(posedge CLKx2);
        dtif.memstore = data_store2;
        @(posedge CLKx2);
        dtif.memstore = data_store3;
        @(posedge CLKx2);
        dtif.memstore = data_store4;
        @(posedge CLK);
        
        dtif.clear = 1'b1;
        dtif.wr_en = 1'b0;
        @(posedge CLK);

    endtask

    task read (
        
    );

        dtif.rd_en = 1'b1;
        dtif.clear = 1'b0;
        DQ_tb = 8'h00;
        DQS_t_tb = 1'b1;
        @(posedge CLKx2);
        DQS_t_tb = 1'b0;
        @(posedge CLKx2);

        DQ_tb = 8'hAB;
        DQS_t_tb = 1'b1;
        @(posedge CLKx2);
        DQ_tb = 8'hCD;
        DQS_t_tb = 1'b0;
        
        @(posedge CLKx2);

        DQ_tb = 8'hEE;
        DQS_t_tb = 1'b1;
        
        @(posedge CLKx2);
        DQ_tb = 8'hFF;
        DQS_t_tb = 1'b0;  
        @(posedge CLKx2);

        DQ_tb = 8'hAA;
        DQS_t_tb = 1'b1;  
        @(posedge CLKx2);

        DQ_tb = 8'hBB;
        DQS_t_tb = 1'b0;  
        @(posedge CLKx2);

        DQ_tb = 8'hCC;
        DQS_t_tb = 1'b1;  
        @(posedge CLKx2);

        DQ_tb = 8'hDD;
        DQS_t_tb = 1'b0;  
        @(posedge CLKx2);


        repeat (4) @(posedge CLK);
        dtif.clear = 1'b1;
        dtif.rd_en = 1'b0;
        @(posedge CLK);

    endtask   
    initial begin
        dtif.wr_en  = 1'b0;
        dtif.rd_en = 1'b0;
        dtif.clear = 1'b0;
        dtif.memstore = '0;
        #(10000);
        nRST = 1'b1;
        @(posedge CLK);
        nRST = 1'b0;
        @(posedge CLK);
        @(posedge CLK);
        nRST = 1'b1;

        @(posedge CLK);
        @(posedge CLK);

        write (.data_store1(32'hAAAA_AAAA), .data_store2(32'hBBBB_BBBB), .data_store3(32'hCCCC_CCCC), .data_store4(32'hDDDD_DDDD), .COL_choice (3'd2));
        read ();
        repeat(10) @(posedge CLK);
        // #(10000);

        $finish();

    end


endmodule