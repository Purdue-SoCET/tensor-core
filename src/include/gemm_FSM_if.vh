
`ifndef  GEMM_FSM_IF_VH
`define GEMM_FSM_IF_VH
`include "sp_types_pkg.vh"
import sp_types_pkg::*;


interface gemm_FSM_if;

    gemmFIFO_t gemmFIFO0_rdata, gemmFIFO1_rdata, gemmFIFO2_rdata, gemmFIFO3_rdata;
    logic gemmFIFO0_empty, gemmFIFO1_empty, gemmFIFO2_empty, gemmFIFO3_empty, drained, fifo_has_space, new_weight;
    logic [BITS_PER_ROW-1:0] weight_input_data, partial_sum_data;
    logic [ROW_S_W-1:0] weight_input_row_sel, partial_sum_row_sel;
    logic input_enable, partial_enable, weight_enable, gemmFIFO0_REN, gemmFIFO1_REN, gemmFIFO2_REN, gemmFIFO3_REN;


    modport sp (
        input gemmFIFO0_rdata, gemmFIFO1_rdata, gemmFIFO2_rdata, gemmFIFO3_rdata, gemmFIFO0_empty, 
        gemmFIFO1_empty, gemmFIFO2_empty, gemmFIFO3_empty, drained, fifo_has_space, new_weight,
        output weight_input_data, partial_sum_data, weight_input_row_sel, partial_sum_row_sel, input_enable, 
        partial_enable, weight_enable, gemmFIFO0_REN, gemmFIFO1_REN, gemmFIFO2_REN, gemmFIFO3_REN
    );

endinterface

`endif 

/*
Inputs:
    gemmFIFO0_rdata
    gemmFIFO1_rdata
    gemmFIFO2_rdata
    gemmFIFO3_rdata
    gemmFIFO0_empty
    gemmFIFO1_empty
    gemmFIFO2_empty
    gemmFIFO3_empty
    drained
    fifo_has_space
    new_weight

Outputs:
    weight_input_data
    partial_sum_data
    weight_input_row_sel
    partial_sum_row_sel
    input_enable
    partial_enable
    weight_enable
    gemmFIFO0_REN
    gemmFIFO1_REN
    gemmFIFO2_REN
    gemmFIFO3_REN

*/