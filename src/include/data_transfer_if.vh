`ifndef DATA_TRANSFER_IF
`define DATA_TRANSFER_IF

`include "data_transfer_if.vh"
`include "dram_pkg.vh"

interface data_transfer_if ();
    import dram_pkg::*;

    logic wr_en, rd_en, clear;
    logic edge_flag;
    word_t memstore, memload;
    logic [2:0] COL_choice;
    wire [WORD_W-1 : 0] DQ;
    wire DQS_t, DQS_c, DM_n;
    
    modport data_trans (
        //input wr_en, rd_en, clear, 
        input memstore, COL_choice,
        inout DQ, DQS_t, DQS_c, DM_n,
        output memload, edge_flag
    );

endinterface

`endif