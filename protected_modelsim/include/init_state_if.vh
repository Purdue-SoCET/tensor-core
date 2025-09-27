`ifndef INIT_STATE_IF
`define INIT_STATE_IF

`include "dram_pkg.vh"

interface init_state_if ();
    import dram_pkg::*;

    //Input
    logic init, init_done;
    dram_state_t init_state, ninit_state;

    modport dt (
        input init,
        output init_done, init_state, ninit_state
    );

endinterface

`endif
