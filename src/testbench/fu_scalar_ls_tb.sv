`timescale 1ns / 10ps
`include "fu_scalar_ls_if.vh"

module fu_scalar_ls_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    fu_scalar_ls_if slsif ();

    test PROG (.CLK(CLK), .nRST(nRST), .sls_if(slsif));

    fu_scalar_ls DUT (.CLK(CLK), .nRST(nRST), .sls_if(slsif));

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    fu_scalar_ls_if.tb sls_if
);

    import isa_pkg::*;
    import datapath_pkg::*;

    initial begin 
        nRST = '1;
        sls_if.imm = '0;
        sls_if.mem_type = scalar_mem_t'('0);
        sls_if.rs1 = '0;
        sls_if.rs2 = '0;
        sls_if.dmem_in = '0;
        sls_if.dhit_in = '0;

        @(posedge CLK);
        @(posedge CLK);

        nRST = '0;

        @(posedge CLK);
        @(posedge CLK);

        $finish;
    end

endprogram