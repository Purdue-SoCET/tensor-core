`include "vls_if.vh"
`include "vector_if.vh"
`include "vector_types.vh"

`timescale 1 ns / 1 ns

module vls_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    vls_if vlsif ();
    vls DUT (.CLK(CLK), .nRST(nRST), .vlsif(vlsif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;

    #(PERIOD);

    nRST = 1;

    casenum = 1;
    casename = "Add Case 1: ";

    vaddsubif.enable = 1;
    vaddsubif.sub = 0;
    vaddsubif.port_a = 16'b0_01111_0000000001;
    vaddsubif.port_b = 16'b0_01111_0000000011;

    #(PERIOD);

    casenum = 2;
    casename = "Add Case 2";

    vaddsubif.port_a = 16'b0_10000_0000000001;
    vaddsubif.port_b = 16'b0_01111_0000000011;

    #(PERIOD);

    casenum = 3;
    casename = "Overflow Case";

    vaddsubif.port_a = 16'b0_10000_1000000000;
    vaddsubif.port_b = 16'b0_01111_1100000000;

    `#(PERIOD);

    casenum = 4;
    casename = "Subtract Case 1 w Adder";

    vaddsubif.port_a = 16'b0_10000_1000000000;
    vaddsubif.port_b = 16'b1_01111_1100000000;

    #(PERIOD);

    casenum = 5;
    casename = "Subtract Case 2 w Adder";

    vaddsubif.port_a = 16'b0_10000_1000000000;
    vaddsubif.port_b = 16'b1_10001_0010000000;

    #(PERIOD);

    casenum = 6;
    casename = "Add Case 3 Two Negatives";

    vaddsubif.port_a = 16'b1_10001_0010000000;
    vaddsubif.port_b = 16'b1_10000_1000000000;

    #(PERIOD);

    casenum = 7;
    casename = "Subtract Case 1 Positive - Negative";

    vaddsubif.sub = 1;
    vaddsubif.port_a = 16'b0_10001_0010000000;
    vaddsubif.port_b = 16'b0_10000_1000000000;

    #(PERIOD);

    casenum = 7;
    casename = "Subtract Case 2 Postive - Negative";

    vaddsubif.sub = 1;
    vaddsubif.port_a = 16'b0_10001_0010000000;
    vaddsubif.port_b = 16'b1_10000_1000000000;
    
    #(PERIOD);

    casenum = 8;
    casename = "Subtract Case 3 Negative - Negative";

    vaddsubif.sub = 1;
    vaddsubif.port_a = 16'b1_10001_0010000000;
    vaddsubif.port_b = 16'b1_10000_1000000000;
    
    #(PERIOD);


    $stop;
end
endmodule