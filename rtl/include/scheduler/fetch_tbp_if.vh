`ifndef FETCH_TBP_IF_VH
`define FETCH_TBP_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface fetch_tbp_if;
    import isa_pkg::*;
    import datapath_pkg::*;
    
    // Signals
    /*
        Inputs: 
        pc_res: PC from resolution stage
        bt_res: branch target from resolution stage
        taken_res: 1 if branch taken in resolution stage
        enable_res: enable signal from resolution stage

        pc_fetch: PC from fetch stage
        enable_fetch: enable signal (if BYTPE instruction) from fetch 
    */
    word_t pc_res, bt_res;
    logic taken_res;
    logic enable_res;

    word_t pc_fetch;
    logic enable_fetch;

    /*
        Outputs: 
        nxt_PC : next PC prediction
    */
    word_t nxt_PC;

    modport tbp (
        input pc_res, bt_res, taken_res, enable_res, pc_fetch, enable_fetch,
        output nxt_PC
    );

    modport tb (
        input nxt_PC,
        output pc_res, bt_res, taken_res, enable_res, pc_fetch, enable_fetch
    );
endinterface
`endif
