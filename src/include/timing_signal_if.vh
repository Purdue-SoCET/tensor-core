`ifndef TIMING_SIGNAL_IF_VH
`define TIMING_SIGNAL_IF_VH

`include "dram_pkg.vh"

interface timing_signal_if;
    import dram_pkg::*;

    logic tACT_done;
    logic tWR_done;
    logic tRD_done;
    logic tPRE_done;
    logic tREF_done;
    logic rf_req;

    logic wr_en, rd_en, clear;
    logic init_done;

    modport cmd_fsm (
        input tACT_done, tWR_done, tRD_done, tPRE_done, tREF_done, rf_req
    );

    modport timing_ctrl (
        input init_done,
        output wr_en, rd_en, clear,
        output tACT_done, tWR_done, tRD_done, tPRE_done, tREF_done, rf_req
    );

endinterface

`endif //TIMING_SIGNAL_IF_VH