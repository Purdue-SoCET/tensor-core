`ifndef ADDRESS_MAPPER_IF_VH
`define ADDRESS_MAPPER_IF_VH

`include "dram_pkg.vh"

interface address_mapper_if;
    
    // import address related parameters
    import dram_pkg::*;

    word_t address;
    configs_t configs;
    logic [RANK_BITS - 1:0] rank;
    logic [BANK_GROUP_BITS - 1:0] BG;
    logic [BANK_BITS - 1:0] bank;
    logic [ROW_BITS - 1:0] row;
    logic [COLUMN_BITS - 1:0] col;
    logic [OFFSET_BITS - 1:0] offset;
    logic [IGNORE_BITS - 1:0] ignore;

    modport addr_mapper (
        input  address, configs,
        output rank, BG, bank, row, col, offset, ignore
    );

    modport cmd_fsm (
        input rank, BG, bank, row, col, offset, ignore
    );

    modport row_open (
        input row, bank, BG
    );

endinterface

`endif // ADDRESS_MAPPER_IF_VH