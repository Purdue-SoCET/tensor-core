`ifndef  SCRATCHPAD_IF_VH
`define SCRATCHPAD_IF_VH
`include "types_pkg.vh"
import sp_types_pkg::*;

interface scratchpad_if;
    
    
    
    logic instrFIFO_WEN, psumout_en, drained, fifo_has_space, sLoad_hit, sStore_hit;
    instrFIFO_t instrFIFO_wdata;
    logic [ROW_S_W-1:0] psumout_row_sel_in, sLoad_row;
    logic [BITS_PER_ROW-1:0] psumout_data, load_data;
    logic [BITS_PER_ROW-1:0] psumout_data, load_data;

    logic instrFIFO_full, partial_enable, weight_enable, input_enable, sLoad, sStore, gemm_complete, load_complete, store_complete;
    logic [BITS_PER_ROW-1:0] weight_input_data, partial_sum_data, store_data;
    logic [ROW_S_W-1:0] weight_input_row_sel, partial_sum_row_sel;
    logic [WORD_W-1:0] load_addr, store_addr;





    modport sp (
        input instrFIFO_WEN, psumout_en, drained, fifo_has_space, sLoad_hit, sStore_hit, 
        instrFIFO_wdata, psumout_row_sel_in, sLoad_row, psumout_data, load_data,
        output instrFIFO_full, partial_enable, weight_enable, input_enable, sLoad, sStore,
        weight_input_data, partial_sum_data, store_data, weight_input_row_sel, partial_sum_row_sel,
        load_addr, store_addr, gemm_complete, load_complete, store_complete
    );

    modport tb (
        output instrFIFO_WEN, psumout_en, drained, fifo_has_space, sLoad_hit, sStore_hit, 
        instrFIFO_wdata, psumout_row_sel_in, sLoad_row, psumout_data, load_data,
        input instrFIFO_full, partial_enable, weight_enable, input_enable, sLoad, sStore,
        weight_input_data, partial_sum_data, store_data, weight_input_row_sel, partial_sum_row_sel,
        load_addr, store_addr, gemm_complete, load_complete
    );

    modport arbiter (
        input store_data, load_addr, store_addr, sLoad, sStore,
        output load_data, sLoad_hit, sStore_hit, sLoad_row
    );
    
    modport testbench (
            output sLoad, sStore, load_addr, store_addr, store_data,
            input load_data, sLoad_hit, sStore_hit, sLoad_row
        );
    modport testbench (
            output sLoad, sStore, load_addr, store_addr, store_data,
            input load_data, sLoad_hit, sStore_hit, sLoad_row
        );

endinterface

`endif 

    /*
    Inputs:
    instrFIFO_WEN
    instrFIFO_wdata
    psumout_en
    psumout_row_sel_in
    psumout_data
    drained
    fifo_has_space

    load_data
    sLoad_hit
    sLoad_row
    sStore_hit




    Outputs:
    instrFIFO_full
    partial_enable
    weight_enable
    input_enable
    weight_input_data
    partial_sum_data
    weight_input_row_sel
    partial_sum_row_sel

    load_addr
    sLoad
    store_data
    store_addr
    sStore


    */
