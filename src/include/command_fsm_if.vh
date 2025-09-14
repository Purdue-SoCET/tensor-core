`ifndef COMMAND_FSM_IF_VH
`define COMMAND_FSM_IF_VH

`include "dram_pkg.vh"

interface command_fsm_if ();
    
    import dram_pkg::*;
    logic dREN, dWEN;
    logic init_done, init_req;
    logic tACT_done, tWR_done, tRD_done;
    logic tPRE_done, tREF_done, rf_req;

    logic [1:0] row_stat;
    cmd_fsm_t cmd_state, ncmd_state;

    modport dut (
        input dREN, dWEN, init_done,
        input tACT_done, tWR_done, tRD_done,
        input tPRE_done, tREF_done, rf_req,
        input row_stat,
        output cmd_state, ncmd_state, init_req
    );

    modport timing_ctrl (
        output cmd_state
    );

endinterface

`endif //COMMAND_FSM_IF_VH