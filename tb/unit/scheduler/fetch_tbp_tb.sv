`timescale 1ns / 10ps
`include "isa_types.vh"
`include "datapath_types.vh"
`include "fetch_tbp_if.vh"

module fetch_tbp_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    fetch_tbp_if fetch_tbpif ();
    fetch_tbp DUT (.CLK(CLK), .nRST(nRST), .tbpif(fetch_tbpif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;
    #(PERIOD)

    $finish;
end
endmodule