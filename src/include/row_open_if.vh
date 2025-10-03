`ifndef ROW_OPEN_IF
`define ROW_OPEN_IF

`include "dram_pkg.vh"

interface row_open_if();
    import dram_pkg::*;
    //We are following 512 x 8 addressing map
    // logic [ROW_BITS - 1:0]              row;
    // logic [BANK_BITS - 1:0]             bank;
    // logic [BANK_GROUP_BITS - 1:0]       bank_group;

    //Conflicted row
    logic [ROW_BITS - 1:0]              row_conflict;

    //Memory request
    logic req_en, refresh, row_resolve;
    logic [1:0] row_stat; //00 IDLE, 01 HIT, 10 MISS, 11 CONFLICT

    modport row_open (
        // input bank_group, bank, row, req_en, refresh, row_resolve,
        input req_en, refresh, row_resolve,
        output row_stat, row_conflict
    );

    modport cmd_fsm (
        input row_stat
    );

    modport tb  (
        input  row_stat, row_conflict,
        // output req_en, refresh, bank_group, bank, row
        output req_en
    );
endinterface
`endif