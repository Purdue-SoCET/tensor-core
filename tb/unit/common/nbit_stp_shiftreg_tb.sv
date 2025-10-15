`timescale 1ns / 10ps
`include "isa_types.vh"
`include "datapath_types.vh"
`include "bpt_tbp_if.vh"

module nbit_stp_shiftreg_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST, enable, in;
    logic [2:0] out;

    always #(PERIOD/2) CLK++;

    nbit_stp_shiftreg DUT (CLK, nRST, enable, in, out);

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;
    enable ='0;
    in = '0;

    #(PERIOD);
    nRST = 1;
    #(PERIOD);

    //Test Case 1: Not enable
    casenum += 1;
    casename = "not enable";
    enable ='0;
    
    in = '0;
    #(PERIOD);
    in = '1;
    #(PERIOD);
    in = '0;
    #(PERIOD);
    in = '1;
    #(PERIOD);

    //Test Case 1: Enable

    casenum += 1;
    casename = "enable";
    enable ='1;
    
    in = '0;
    #(PERIOD);
    in = '1;
    #(PERIOD);
    in = '0;
    #(PERIOD);
    in = '1;
    #(PERIOD);

    $finish;
end
endmodule