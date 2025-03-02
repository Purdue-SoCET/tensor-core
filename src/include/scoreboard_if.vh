`ifndef SCOREBOARD_IF_VH
`define SCOREBOARD_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface scoreboard_if;
    import isa_pkg::*;
    import datapath_pkg::*;

    // inputs
    fetch_t fetch;
    logic flush, freeze;

    wb_t wb;
    wb_ctr_t wb_ctrl;
    word_t s_wdata;

    // execute signals
    logic branch_miss, branch_resolved;
    fu_done_signals fu_ex;

    issue_t out;
    
    modport SB (
        input fetch, flush, wb, s_wdata, wb_ctrl, branch_miss, branch_resolved, fu_ex,
        output out, freeze
    );

    modport tb (
        input out, freeze,
        output fetch, flush, wb, s_wdata, wb_ctrl, branch_miss, branch_resolved, fu_ex
    );
    

endinterface
`endif
