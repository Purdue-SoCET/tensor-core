`timescale 1ns / 10ps
`include "isa_types.vh"
`include "datapath_types.vh"
`include "bpt_tbp_if.vh"

module bpt_tbp_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    bpt_tbp_if bpt_tbpif ();
    bpt_tbp DUT (.CLK(CLK), .nRST(nRST), .bpt_tbpif(bpt_tbpif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;
    bpt_tbpif.pc_res = '0;
    bpt_tbpif.taken_res = '0;
    bpt_tbpif.enable_res = '0;
    bpt_tbpif.pc_fetch = '0;
    #(PERIOD);
    nRST = 1;
    #(PERIOD);

    //Test Case 1: Strongly Not Taken -> Weakly Not Taken -> Strongly Taken
    casenum += 1;
    casename = "Strongly Pred0 (00) -> Weakly Pred0 (01) -> Strongly Pred1 (11) -> Weakly Pred1 (10)  -> Strongly Pred0 (00)";

    bpt_tbpif.enable_res = '1;
    bpt_tbpif.taken_res = 2'b10;

    for (int i = 0; i < 8192; i = i+4) begin
        bpt_tbpif.pc_res = i;
        #(PERIOD);
    end

    for (int i = 0; i < 8192; i = i+4) begin
        bpt_tbpif.pc_res = i;
        #(PERIOD);
    end

    bpt_tbpif.taken_res = 2'b01;

    for (int i = 0; i < 8192; i = i+4) begin
        bpt_tbpif.pc_res = i;
        #(PERIOD);
    end

    for (int i = 0; i < 8192; i = i+4) begin
        bpt_tbpif.pc_res = i;
        #(PERIOD);
    end

    bpt_tbpif.enable_res = '0;
    #(PERIOD);

    //Test Case 2: Read bpt_tbp
    // casenum += 1;
    // casename = "Read bpt_tbp";

    // bpt_tbpif.pc_res = '0;
    // bpt_tbpif.enable_res = '0;
    // #(PERIOD);

    // for (int i = 0; i < 8192; i = i+4) begin
    //     bpt_tbpif.pc_fetch = i;
    //     #(PERIOD);
    // end

    $finish;
end
endmodule