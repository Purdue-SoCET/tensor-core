`ifndef BPT_IF_VH
`define BPT_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface bpt_if;
    import isa_pkg::*;
    import datapath_pkg::*;
    
    // Signals
    /*
        Inputs: 
        pc_res: PC from resolution stage
        taken_res: 1 if branch taken in resolution stage
        enable_res: enable signal from resolution stage

        pc_fetch: PC from fetch stage
    */
    word_t pc_res;
    logic taken_res;
    logic enable_res;

    word_t pc_fetch;

    /*
        Outputs: 
        pred_fetch: prediction from fetch stage
        pred_correct: 1 if prediction was correct (for updating tp_bpt)
    */
    logic pred_fetch;
    logic pred_correct;

    modport bpt (
        input pc_res, taken_res, enable_res, pc_fetch,
        output pred_fetch, pred_correct
    );

    modport tb (
        input pred_fetch, pred_correct,
        output pc_res, taken_res, enable_res, pc_fetch
    );

endinterface
`endif
