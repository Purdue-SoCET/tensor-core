`ifndef DRAM_TOP_VH
`define DRAM_TOP_VH
`include "dram_pkg.vh"


interface dram_top_if();
    import dram_pkg::*;

    logic dWEN, dREN, ram_wait;
    logic [31:0] ram_addr;
    word_t ramload, ramstore;


    //Interface debug for the command FSM
    logic init_done, init_req;
    logic tACT_done, tWR_done, tRD_done;
    logic tPRE_done, tREF_done, rf_req;

    modport csm_debug (
        input tACT_done, tWR_done, tRD_done,
        input tPRE_done, tREF_done, rf_req
    );
    modport dut (
        input dWEN, dREN, ram_addr, ramstore,
        output ramload, ram_wait
    );
    

endinterface

`endif