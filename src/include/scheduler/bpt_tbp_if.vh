`ifndef BPT_TBP_IF_VH
`define BPT_TBP_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface bpt_tbp_if;
    import isa_pkg::*;
    import datapath_pkg::*;
    
    // Signals
    /*
        Inputs: 
        pc_res: PC from resolution stage
        taken_res: concatenation of taken from both predictors
        [1/0] -> predictor 1 taken, predictor 2 not takenf
        enable_res: enable signal from resolution stage

        pc_fetch: PC from fetch stage
    */
    word_t pc_res;
    logic [1:0] taken_res;
    logic enable_res;

    word_t pc_fetch;

    /*
        Outputs: 
        pred_fetch: prediction for fetch stage
    */
    logic pred_fetch;

    modport bpt_tbp (
        input pc_res, taken_res, enable_res, pc_fetch,
        output pred_fetch
    );

    modport tb (
        input pred_fetch,
        output pc_res, taken_res, enable_res, pc_fetch
    );

endinterface
`endif
