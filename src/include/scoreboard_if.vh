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

    wb_ctr_t wb;
    regbits_t s_wdata;

    issue_t out;
    
    modport SB (
        input fetch, flush, freeze, wb, s_wdata,
        output out
    );

    modport tb (
        input out,
        output fetch, flush, freeze, wb, s_wdata
    );
    

endinterface
`endif
