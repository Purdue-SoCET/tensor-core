`ifndef  SCRATCHPAD_IF_VH
`define SCRATCHPAD_IF_VH
// `include "types_pkg.vh"

interface scratchpad_if;
    // import types_pkg::*;

    // COPIED FROM TYPES PACKAGE
    parameter WORD_W = 32;
    parameter REG_W  = 5;
    parameter MATRIX_W = 4;
    parameter VALUE_BITS = 16;
    parameter BITS_PER_ROW = MATRIX_W * VALUE_BITS;

    parameter FU_S_W = 2;
    parameter FU_M_W = 1;
    parameter MAT_S_W = 2;
    parameter ROW_S_W = 2;

    
    logic instrFIFO_WEN, psumout_en, drained, fifo_has_space, sLoad_hit, sStore_hit;
    logic [2+MAT_S_W+ROW_S_W+WORD_W-1:0] instrFIFO_wdata;
    logic [ROW_S_W-1:0] psumout_row_sel_in, sLoad_row;
    logic [BITS_PER_ROW-2:0] psumout_data, load_data;

    logic instrFIFO_full, partial_enable, weight_enable, input_enable, sLoad, sStore, gemm_complete;
    logic [BITS_PER_ROW-1:0] weight_input_data, partial_sum_data, store_data;
    logic [ROW_S_W-1:0] weight_input_row_sel, partial_sum_row_sel;
    logic [WORD_W-1:0] load_addr, store_addr;

    modport sp (
        input instrFIFO_WEN, psumout_en, drained, fifo_has_space, sLoad_hit, sStore_hit, 
        instrFIFO_wdata, psumout_row_sel_in, sLoad_row, psumout_data, load_data,
        output instrFIFO_full, partial_enable, weight_enable, input_enable, sLoad, sStore,
        weight_input_data, partial_sum_data, store_data, weight_input_row_sel, partial_sum_row_sel,
        load_addr, store_addr, gemm_complete
    );

    modport arbiter (
        input store_data, load_addr, store_addr, sLoad, sStore,
        output load_data, sLoad_hit, sStore_hit, sLoad_row
    );
    

endinterface

`endif 