`include "vreduction_alu_if.vh"
`include "vector_types.vh"

module vreduction_alu_tb;
    import vector_pkg::*;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    vreduction_alu_if alu_if ();
    vreduction_alu DUT (.CLK(CLK), .nRST(nRST), .vraluif(alu_if));

    int casenum;
    string casename;

initial begin
    casenum = 0;
    casename = "nRST";

    nRST = 'b0;

    #(PERIOD);

    nRST = 1;

    // ---------------- MIN cases ----------------
    casenum = 1;
    casename = "Min Case 1: Two Positive";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'h4000; // +2.0
    #(PERIOD);

    casenum = 2;
    casename = "Min Case 2: Two Negative";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'hBA00; // -0.75
    alu_if.value_b = 16'hC000; // -2.0
    #(PERIOD);

    casenum = 3;
    casename = "Min Case 3: Positive and Negative";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'hBA00; // -0.75
    #(PERIOD);

    casenum = 4;
    casename = "Min Case 4: Positive and Positive Infinity";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'h7C00; // +Inf
    #(PERIOD);

    casenum = 5;
    casename = "Min Case 5: Negative and Positive Infinity";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'hBA00; // -0.75
    alu_if.value_b = 16'h7C00; // +Inf
    #(PERIOD);

    casenum = 6;
    casename = "Min Case 6: Positive and Negative Infinity";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'hFC00; // -Inf
    #(PERIOD);

    casenum = 7;
    casename = "Min Case 7: Negative and Negative Infinity";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'hBA00; // -0.75
    alu_if.value_b = 16'hFC00; // -Inf
    #(PERIOD);

    casenum = 8;
    casename = "Min Case 8: Negative Infinity and Positive Infinity";
    alu_if.alu_op = VR_MIN;
    alu_if.value_a = 16'hFC00; // -Inf
    alu_if.value_b = 16'h7C00; // +Inf
    #(PERIOD);

    // ---------------- MAX cases ----------------
    casenum = 9;
    casename = "Max Case 1: Two Positive";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'h4000; // +2.0
    #(PERIOD);

    casenum = 10;
    casename = "Max Case 2: Two Negative";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'hBA00; // -0.75
    alu_if.value_b = 16'hC000; // -2.0
    #(PERIOD);

    casenum = 11;
    casename = "Max Case 3: Negative and Positive";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'hC000; // -2.0
    alu_if.value_b = 16'h3E00; // +1.5
    #(PERIOD);

    casenum = 12;
    casename = "Max Case 4: Positive and Positive Infinity";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'h7C00; // +Inf
    #(PERIOD);

    casenum = 13;
    casename = "Max Case 5: Negative and Positive Infinity";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'hBA00; // -0.75
    alu_if.value_b = 16'h7C00; // +Inf
    #(PERIOD);

    casenum = 14;
    casename = "Max Case 6: Positive and Negative Infinity";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'h3E00; // +1.5
    alu_if.value_b = 16'hFC00; // -Inf
    #(PERIOD);

    casenum = 15;
    casename = "Max Case 7: Negative and Negative Infinity";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'hBA00; // -0.75
    alu_if.value_b = 16'hFC00; // -Inf
    #(PERIOD);

    casenum = 16;
    casename = "Max Case 8: Positive Infinity and Negative Infinity";
    alu_if.alu_op = VR_MAX;
    alu_if.value_a = 16'h7C00; // +Inf
    alu_if.value_b = 16'hFC00; // -Inf
    #(PERIOD);

    $stop;

end
endmodule