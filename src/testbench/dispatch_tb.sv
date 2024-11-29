`timescale 1ns / 10ps
`include "dispatch_if.vh"

// module dispatch_tb();

// // Parameters
// localparam CLK_PERIOD = 1;

// // Testbench Signals
// logic tb_clk;
// logic tb_nrst;
// logic fetch;
// logic flush;
// logic freeze;
// logic [2:0] fu_busy;
// logic ihit;

// always
// begin
//     tb_clk = 1'b0;
//     #(CLK_PERIOD/2.0);
//     tb_clk = 1'b1;
//     #(CLK_PERIOD/2.0);
// end

// dispatch_if diif_tb();

// dispatch DUT (.nRST(tb_nrst), .CLK(tb_clk), .diif(diif_tb));

// initial begin

//     // Testbench Signals
//     tb_nrst = 1'b1;

//     // Dispatch Interface
//     fetch = '0;
//     flush = '0;
//     freeze = '0;
//     fu_busy = '0;
//     ihit = '0;

//     #(CLK_PERIOD*2);

//     // Power on Reset
//     tb_nrst = 1'b0;
//     #(CLK_PERIOD*2);
//     tb_nrst = 1'b1;
//     #(CLK_PERIOD*2);

//     $stop;
// end

// endmodule

module dispatch_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    dispatch_if diif ();

    test PROG (.CLK(CLK), .nRST(nRST), .dis_if(diif));

    dispatch DUT (.CLK(CLK), .nRST(nRST), .diif(diif));

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    dispatch_if.tb dis_if
);
    initial begin
        nRST = 0;
        dis_if.fetch = '0; 
        dis_if.flush = '0;
        dis_if.freeze = '0;
        dis_if.fust_s = '0;
        dis_if.fust_m = '0; 
        dis_if.fust_g = '0;
        dis_if.wb = '0;
        dis_if.wb.m_rw_en = '0;
        dis_if.ihit = '0;

        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);

        $finish;
    end


endprogram