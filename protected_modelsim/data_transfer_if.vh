`ifndef DATA_TRANSFER_IF
`define DATA_TRANSFER_IF
`include "data_transfer_if.vh"
`include "dram_command_if.vh"

interface data_transfer_if ();
    import dram_pack::*;

    parameter WORD_W = 32;

    logic wr_en, rd_en, clear;
    logic [WORD_W - 1: 0] memstore, memload;
    wire [CONFIGURED_DQ_BITS - 1 : 0] DQ;
    wire DQS_t, DQS_c;

    modport data_trans (
        input wr_en, rd_en, clear, memstore,
        inout DQ, DQS_t, DQS_c,
        output memload
    );

endinterface

`endif