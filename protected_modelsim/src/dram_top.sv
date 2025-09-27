`timescale 1ps/1ps
`include "dram_top_if.vh"
`include "control_unit_if.vh"
`include "signal_gen_if.vh"

module dram_top (
    input logic CLK,
    input logic nRST,
    control_unit_if.arb myctrl,
    control_unit_if.dram_sig myctrl_sig,
    signal_gen_if.dut mysig
);

    assign mysig.ref_re = myctrl_sig.rf_req;
    assign mysig.state =  myctrl_sig.state;
    assign mysig.nstate = myctrl_sig.state;
    assign mysig.RA0 =     myctrl_sig.rank;
    assign mysig.BG0 =     myctrl_sig.BG;
    assign mysig.BA0=      myctrl_sig.bank;
    assign mysig.R0=      myctrl_sig.row;
    assign mysig.C0=      myctrl_sig.col;

    control_unit ctrl (.CLK(CLK), .nRST(nRST), .mytop(myctrl), .mysig(myctrl_sig));
    signal_gen sig_gen (.CLK(CLK), .nRST(nRST), .mysig(mysig));


endmodule
