`timescale 1ns / 10ps
`include "isa_types.vh"
`include "datapath_types.vh"
`include "btb_if.vh"

module btb_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    btb_if btbif ();
    btb DUT (.CLK(CLK), .nRST(nRST), .btbif(btbif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;
    btbif.pc_res = '0;
    btbif.bt_res = '0;
    btbif.enable_res = '0;
    btbif.pc_fetch = '0;
    #(PERIOD);
    nRST = 1;
    #(PERIOD);

    //Test Case 1: Fill BTB
    casenum += 1;
    casename = "Fill BTB";

    btbif.enable_res = '1;
    #(PERIOD);

    for (int i = 0; i < 8192; i = i+4) begin
        btbif.pc_res = i;
        btbif.bt_res = i;
        #(PERIOD);
    end

    #(PERIOD);

    //Test Case 2: Read BTB
    casenum += 1;
    casename = "Read BTB";

    btbif.pc_res = '0;
    btbif.bt_res = '0;
    btbif.enable_res = '0;
    #(PERIOD);

    for (int i = 0; i < 8192; i = i+4) begin
        btbif.pc_fetch = i;
        #(PERIOD);
    end

    $finish;
end
endmodule