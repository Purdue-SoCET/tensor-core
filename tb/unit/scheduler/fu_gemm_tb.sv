`timescale 1ns / 10ps
`include "fu_gemm_if.vh"
`include "isa_types.vh"
`include "datapath_types.vh"

module fu_gemm_tb;

    parameter PERIOD = 2;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    fu_gemm_if fugif ();
    fu_gemm DUT (.CLK(CLK), .nRST(nRST), .fugif(fugif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;
    fugif.gemm_enable = '0;
    fugif.new_weight_in = '0;
    fugif.rs1_in = '0;
    fugif.rs2_in = '0;
    fugif.rs3_in = '0;
    fugif.rd_in = '0;

    #(PERIOD);

    nRST = 1;

    #(PERIOD);

    //Test Case 1: Normal Input
    casenum += 1;
    casename = "Normal Input";

    fugif.gemm_enable = '1;
    fugif.new_weight_in = '0;
    fugif.rs1_in = 'h1;
    fugif.rs2_in = 'h2;
    fugif.rs3_in = 'h3;
    fugif.rd_in = 'h4;

    #(PERIOD);
    fugif.gemm_enable = '0;
    fugif.new_weight_in = '0;
    fugif.rs1_in = '0;
    fugif.rs2_in = '0;
    fugif.rs3_in = '0;
    fugif.rd_in = '0;
    #(PERIOD);

    //Test Case 2: Differnt RS1, new_weight = 1
    casenum += 1;
    casename = "Differnt RS1, new_weight = 1";

    fugif.gemm_enable = '1;
    fugif.new_weight_in = '1;
    fugif.rs1_in = 'h2;
    fugif.rs2_in = 'h2;
    fugif.rs3_in = 'h3;
    fugif.rd_in = 'h4;

    #(PERIOD);
    fugif.gemm_enable = '0;
    fugif.new_weight_in = '0;
    fugif.rs1_in = '0;
    fugif.rs2_in = '0;
    fugif.rs3_in = '0;
    fugif.rd_in = '0;
    #(PERIOD);

    $finish;
end
endmodule