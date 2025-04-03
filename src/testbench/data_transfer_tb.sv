`timescale 1ns / 1ps
`include "data_transfer_if.vh"
`include "dram_command_if.vh"

module data_transfer_tb();
    import dram_pack::*;
    localparam CLK_PERIOD = 10;
    logic CLK;
    logic nRST;
    logic [CONFIGURED_DQ_BITS - 1:0] DQ_tb;
    logic [CONFIGURED_DQS_BITS - 1 :0] DQS_t_tb, DQS_c_tb;

    data_transfer_if dtif();

    data_transfer DUT (
        .CLK(CLK),
        .nRST(nRST),
        .mydata(dtif)
    );

    always begin
        CLK = 1'b0;
        #(CLK_PERIOD / 2.0);
        CLK = 1'b1;
        #(CLK_PERIOD / 2.0);
    end

    assign dtif.DQ    = (dtif.rd_en) ? DQ_tb : 'z;
    assign dtif.DQS_t = (dtif.rd_en) ? DQS_t_tb:  'z;
    assign dtif.DQS_c = (dtif.rd_en) ? DQS_c_tb:   'z; 
    task write (
        input logic [31:0] data_store
    );

        dtif.wr_en = 1'b1;
        dtif.memstore = data_store;
        
        repeat (4) @(posedge CLK);
        dtif.clear = 1'b1;
        dtif.wr_en = 1'b0;
        @(posedge CLK);

    endtask

    task read (
        
    );

        dtif.rd_en = 1'b1;
        dtif.clear = 1'b0;
        DQ_tb = 8'hAB;
        DQS_t_tb = 1'b1;
        DQS_c_tb = 1'b0;
        #(CLK_PERIOD / 2);
        DQ_tb = 8'hCD;
        DQS_t_tb = 1'b0;
        DQS_c_tb = 1'b1;
        #(CLK_PERIOD / 2);

        DQ_tb = 8'hEE;
        DQS_t_tb = 1'b1;
        DQS_c_tb = 1'b0;
        #(CLK_PERIOD / 2);
        DQ_tb = 8'hFF;
        DQS_t_tb = 1'b0;
        DQS_c_tb = 1'b1;
        #(CLK_PERIOD / 2);


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

        nRST = 1'b1;
        @(posedge CLK);
        nRST = 1'b0;
        @(posedge CLK);
        @(posedge CLK);
        nRST = 1'b1;

        @(posedge CLK);
        @(posedge CLK);

        write (.data_store(32'h0000DEAD));
        read ();
        repeat(10) @(posedge CLK);

        $finish();

    end


endmodule