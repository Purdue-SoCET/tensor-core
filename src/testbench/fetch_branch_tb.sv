`timescale 1ns / 10ps
`include "fetch_branch_if.vh"
`include "isa_types.vh"
`include "datapath_types.vh"
`include "fetch_if.vh"
`include "fu_branchpred_if.vh"
`include "fu_branch_if.vh"

module fetch_branch_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    fetch_branch_if fbif ();
    fetch_if fif();
    fu_branchpred_if fbpif();
    fu_branch_if fufif();

    test PROG (.CLK(CLK), .nRST(nRST), .fbif(fbif));

    fetch_branch DUT (.CLK(CLK), .nRST(nRST), .fbif(fbif));
    fetch DUT1 (.CLK(CLK), .nRST(nRST), .fif(fif));
    fu_branchpred DUT2 (.CLK(CLK), .nRST(nRST), .fbpif(fbpif));
    fu_branch DUT3 (.CLK(CLK), .nRST(nRST), .fufif(fufif));

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    fetch_branch_if.tb fbif
);
initial begin
    parameter PERIOD = 1;
    nRST = 0;
    #(PERIOD * 10);

    nRST = 1;

    fbif.branch_type = 2'b00;
    fbif.branch = 1;
    fbif.branch_gate_sel = 0;
    fbif.reg_a = 32'd20;
    fbif.reg_b = 32'd20;
    fbig.current_pc = 32'hF01ADA44;
    fbif.imm = 32'd80; //immediate branch value
    
    #(PERIOD * 10); //modulate the first value for the branch predictor module

    fbif.branch_type = 2'b00;
    fbif.branch = 1;
    fbif.branch_gate_sel = 0;
    fbif.reg_a = 32'd20;
    fbif.reg_b = 32'd20;
    fbig.current_pc = 32'hF01ADA44;
    fbif.imm = 32'd80; //see if the branch predictor is usedn again

    #(PERIOD * 10);

    fbif.branch_type = 2'b00;
    fbif.branch = 1;
    fbif.branch_gate_sel = 1;
    fbif.reg_a = 32'd20; //same pc but now branch outcome should be false for a beq
    fbif.reg_b = 32'd10;
    fbig.current_pc = 32'hF01ADA44;
    fbif.imm = 32'd80; //branch predictor should produce a false outcome and fetch should therefore flush

    #(PERIOD * 10);


    $finish;
end
endprogram 
