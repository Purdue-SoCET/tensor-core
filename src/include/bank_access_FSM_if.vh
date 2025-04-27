`ifndef BANK_ACCESS_FM_IF
`define BANK_ACCESS_FM_IF
`include "sp_types_pkg.vh"
import sp_types_pkg::*;

interface bank_access_FSM_if;

    logic sLoad_hit, wFIFO_full, instrFIFO_empty, rFIFO_full, psumoutFIFO_full, new_instr;
    logic [ROW_S_W-1:0] sLoad_row;
    logic [BITS_PER_ROW-1:0] load_data;
    instrFIFO_t instrFIFO_rdata;
    psumoutFIFO_t psumoutFIFO_rdata;
    logic [MAT_S_W+2-1:0] gemm_mat;

    logic instrFIFO_REN, psumoutFIFO_REN, sLoad, wFIFO_WEN, rFIFO_WEN;
    logic [WORD_W-1:0] load_addr;
    wFIFO_t wFIFO_wdata;
    rFIFO_t rFIFO_wdata;

    modport sp(
        input sLoad_hit, wFIFO_full, instrFIFO_empty, rFIFO_full, psumoutFIFO_full, sLoad_row, load_data, instrFIFO_rdata, psumoutFIFO_rdata, gemm_mat, new_instr, 
        output instrFIFO_REN, psumoutFIFO_REN, sLoad, wFIFO_WEN, rFIFO_WEN, load_addr, wFIFO_wdata, rFIFO_wdata
    );

endinterface

`endif 