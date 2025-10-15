`ifndef ROW_OPEN_IF
`define ROW_OPEN_IF
`include "dram_pkg.vh"

interface row_open_if();
    import dram_pkg::*;
    //We are following 512 x 8 addressing map
    logic [ROW_BITS-1:0] row;
    logic [1:0] bank, bank_group;

    //Conflicted row
    logic [ROW_BITS-1:0] row_conflict;
    logic all_row_closed;
    logic tACT_done;

    //Memory request
    logic req_en, refresh, row_resolve;
    logic [1:0] row_stat; //00 IDLE, 01 HIT, 10 MISS, 11 CONFLICT

    modport dut (
        input bank_group, bank, row, req_en, refresh, row_resolve, tACT_done,
        output row_stat, row_conflict, all_row_closed
    );

    modport tb  (
        input  row_stat, row_conflict,
        output req_en, refresh, bank_group, bank, row
    );
endinterface
`endif