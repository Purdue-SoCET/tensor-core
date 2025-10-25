`include "control_unit_if.vh"
`include "signal_gen_if.vh"

module dram_controller_top (
    input logic clk, clkx2,
    input logic nRST,
    signal_gen_if sigif,
    address_mapper_if amif,
    init_state_if initif,
    row_open_if polif,
    command_fsm_if cfsmif,
    timing_signals_if timif,
    control_unit_if cuif,
    data_transfer_if dataif
);

    control_unit    control_unit  (.clk(clk), .nRST(nRST), .amif(amif), .initif(initif), .polif(polif), 
                                   .cfsmif(cfsmif), .timif(timif), .cuif(cuif));
    signal_gen      sig_gen       (.CLK(clk), .nRST(nRST), .cuif(cuif.sig_gen), .mysig(sigif.dram));
    data_transfer   data_transfer (.CLK(clk), .CLKx2(clkx2), .nRST(nRST), .cuif(cuif.data_trans), .mydata(dataif.data_trans));


endmodule