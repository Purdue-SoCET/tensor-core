`include "dram_pkg.vh"
`include "address_mapper_if.vh"
`include "timing_signals_if.vh"
`include "command_fsm_if.vh"
`include "row_open_if.vh"
`include "init_state_if.vh"

module control_unit (
    input logic clk, nRST,
    address_mapper_if amif,
    init_state_if initif,
    row_open_if polif,
    command_fsm_if cfsmif,
    timing_signals_if timif
);
    init_state              init_state      (.CLK(clk), .nRST(nRST), .it(initif));
    addr_mapper             addr_mapper     (.amif(amif.addr_mapper));
    row_open #(.DEPTH(16))  row_open        (.CLK(clk), .nRST(nRST), .pol_if(polif.row_open), .amif(amif.row_open),
                                            .timif(timif.row_open));
    command_FSM             command_fsm     (.CLK(clk), .nRST(nRST), .mycmd(cfsmif.cmd_fsm), .polif(polif.cmd_fsm),
                                            .timif(timif.cmd_fsm));
    timing_control          timing_control  (.clk(clk), .nRST(nRST), .timif(timif.timing_ctrl), 
                                            .cfsmif(cfsmif.timing_ctrl));
endmodule