`timescale 1ns / 10ps
`include "isa_types.vh"
`include "datapath_types.vh"
`include "bpt_if.vh"

module bpt_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    bpt_if bptif ();
    bpt DUT (.CLK(CLK), .nRST(nRST), .bptif(bptif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;
    bptif.pc_res = '0;
    bptif.taken_res = '0;
    bptif.enable_res = '0;
    bptif.pc_fetch = '0;
    #(PERIOD);
    nRST = 1;
    #(PERIOD);

    //Test Case 1: Strongly Not Taken -> Weakly Not Taken -> Strongly Taken
    casenum += 1;
    casename = "Strongly Not Taken (00) -> Weakly Not Taken (01) -> Strongly Taken (11) -> Weakly Taken (10)  -> Strongly Not Taken (00)";

    bptif.enable_res = '1;
    bptif.taken_res = '1;

    for (int i = 0; i < 8192; i = i+4) begin
        bptif.pc_res = i;
        #(PERIOD);
    end

    for (int i = 0; i < 8192; i = i+4) begin
        bptif.pc_res = i;
        #(PERIOD);
    end

    bptif.taken_res = '0;

    for (int i = 0; i < 8192; i = i+4) begin
        bptif.pc_res = i;
        #(PERIOD);
    end

    for (int i = 0; i < 8192; i = i+4) begin
        bptif.pc_res = i;
        #(PERIOD);
    end

    bptif.enable_res = '0;
    #(PERIOD);

    //Test Case 2: Read bpt
    // casenum += 1;
    // casename = "Read bpt";

    // bptif.pc_res = '0;
    // bptif.enable_res = '0;
    // #(PERIOD);

    // for (int i = 0; i < 8192; i = i+4) begin
    //     bptif.pc_fetch = i;
    //     #(PERIOD);
    // end

    $finish;
end
endmodule