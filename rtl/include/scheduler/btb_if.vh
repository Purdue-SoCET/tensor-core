`ifndef BTB_IF_VH
`define BTB_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface btb_if;
    import isa_pkg::*;
    import datapath_pkg::*;
    
    // Signals
    /*
        Inputs: 
        pc_res: PC from resolution stage
        bt_res: branch target from resolution stage
        enable_res: enable signal from resolution stage

        pc_fetch: PC from fetch stage
    */
    word_t pc_res, bt_res;
    logic enable_res;

    word_t pc_fetch;

    /*
        Outputs: 
        bt_fetch: branch target from fetch stage
    */
    word_t bt_fetch;

    modport btb (
        input pc_res, bt_res, enable_res, pc_fetch,
        output bt_fetch
    );

    modport tb (
        input bt_fetch,
        output pc_res, bt_res, enable_res, pc_fetch
    );

endinterface
`endif
