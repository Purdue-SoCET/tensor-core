`ifndef  LOAD_FSM_IF_VH
`define LOAD_FSM_IF_VH
`include "types_pkg.vh"

interface outFIFO_FSM_if;
    import types_pkg::*;

    logic instrFIFO_empty, sLoad_hit, wFIFO0_full, wFIFO1_full, wFIFO2_full, wFIFO3_full, rFIFO0_full, rFIFO1_full, rFIFO2_full, rFIFO3_full, rFIFO0_WEN, rFIFO1_WEN, rFIFO2_WEN, rFIFO3_WEN;
    logic sLoad, wFIFO0_WEN, wFIFO1_WEN, wFIFO2_WEN, wFIFO3_WEN, psumoutFIFO_WEN, psumoutFIFO_full, new_weight;
    logic [ROW_S_W-1:0] sLoad_row;
    logic [BITS_PER_ROW-1:0] load_data;
    logic [2+MAT_S_W+ROW_S_W+WORD_W-1:0] instrFIFO_wdata;
    logic [WORD_W-1:0] load_addr;
    logic [(BITS_PER_ROW+MAT_S_W+ROW_S_W):0] wFIFO0_wdata, wFIFO1_wdata, wFIFO2_wdata, wFIFO3_wdata;
    logic [(WORD_W+MAT_S_W+ROW_S_W+1):0] rFIFO0_wdata, rFIFO1_wdata, rFIFO2_wdata, rFIFO3_wdata;
    logic [BITS_PER_ROW+ROW_S_W-1:0] psumoutFIFO_wdata;


    modport sp (
        input  instrFIFO_wdata, instrFIFO_WEN, sLoad_hit, sLoad_row, load_data, wFIFO0_full, 
        wFIFO1_full, wFIFO2_full, wFIFO3_full, psumoutFIFO_wdata, rFIFO0_full, 
        rFIFO1_full, rFIFO2_full, rFIFO3_full, psumoutFIFO_WEN
        output instrFIFO_full, sLoad, load_addr, wFIFO0_wdata, wFIFO0_WEN, wFIFO1_wdata, wFIFO1_WEN, 
        wFIFO2_wdata, wFIFO2_WEN, wFIFO3_wdata, wFIFO3_WEN, psumoutFIFO_full, new_weight, rFIFO0_wdata, 
        rFIFO1_wdata, rFIFO2_wdata, rFIFO3_wdata, rFIFO0_WEN, rFIFO1_WEN, rFIFO2_WEN, rFIFO3_WEN
    );
    

endinterface

`endif 

/*
rFIFO0_wdata
rFIFO0_WEN
rFIFO1_wdata
rFIFO1_WEN
rFIFO2_wdata
rFIFO2_WEN
rFIFO3_wdata
rFIFO3_WEN
Inputs:
instrFIFO_rdata
instrFIFO_empty
sLoad_hit
sLoad_row
load_data
wFIFO0_full
wFIFO1_full
wFIFO2_full
wFIFO3_full
storeFIFO_REN

Outputs:
instrFIFO_REN
sLoad
load_addr
wFIFO0_wdata
wFIFO0_WEN
wFIFO1_wdata
wFIFO1_WEN
wFIFO2_wdata
wFIFO2_WEN
wFIFO3_wdata
wFIFO3_WEN
storeFIFO_rdata
storeFIFO_empty


*/