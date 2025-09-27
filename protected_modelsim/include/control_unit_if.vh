`ifndef CONTROL_UNIT_VH
`define CONTROL_UNIT_VH
`include "dram_pkg.vh"


interface control_unit_if();
    import dram_pkg::*;

    logic dWEN, dREN, ram_wait;
    logic [31:0] ram_addr;
    word_t ramload, ramstore;

    dram_state_t state, nstate;

    //Interface debug for the command FSM
    logic init_done, init_req;
    logic tACT_done, tWR_done, tRD_done;
    logic tPRE_done, tREF_done, rf_req;

    //Interface for connecting to the signal generator
    logic [RANK_BITS - 1:0] rank;
    logic [BANK_GROUP_BITS - 1:0] BG;
    logic [BANK_BITS - 1:0] bank;
    logic [ROW_BITS - 1:0] row;
    logic [COLUMN_BITS + OFFSET_BITS - 1:0] col;
    logic [OFFSET_BITS-1:0] offset;

    //Interface for connect timing-control_unit-data_transfer
    logic wr_en, rd_en, clear;

    modport csm_debug (
        input tACT_done, tWR_done, tRD_done,
        input tPRE_done, tREF_done, rf_req
    );

    modport arb (
        input dWEN, dREN, ram_addr,
        output ram_wait, wr_en, rd_en, clear, offset
    );

    modport dram_sig (
        output state, nstate, rank, BG, bank, row, col, rf_req
    );
    

endinterface

`endif