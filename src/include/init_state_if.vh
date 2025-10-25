`ifndef INIT_STATE_IF
`define INIT_STATE_IF

`include "dram_pkg.vh"

interface init_state_if ();
    import dram_pkg::*;

    //Input
    logic init, init_valid;
    dram_state_t init_state, n_init_state;

    modport init_fsm (
        input init,
        output init_valid, init_state, n_init_state
    );

endinterface

`endif