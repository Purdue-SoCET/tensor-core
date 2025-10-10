`ifndef TIMING_SIGNALS_IF_VH
`define TIMING_SIGNALS_IF_VH

`include "dram_pkg.vh"

interface timing_signals_if;
    import dram_pkg::*;

    logic tACT_done;
    logic tWR_done;
    logic tRD_done;
    logic tPRE_done;
    logic tREF_done;
    logic rf_req;
    logic wr_en;
    logic rd_en;
    logic clear;   // everytime done

    modport cmd_fsm (
        input tACT_done, tWR_done, tRD_done, tPRE_done, tREF_done, rf_req
    );

    modport timing_ctrl (
        output tACT_done, tWR_done, tRD_done, tPRE_done, tREF_done, rf_req, wr_en, rd_en, clear
    );

    modport data_transfer (
        input wr_en, rd_en, clear
    );

    modport row_open (
        input tREF_done
    );

endinterface

`endif //TIMING_SIGNALS_IF_VH