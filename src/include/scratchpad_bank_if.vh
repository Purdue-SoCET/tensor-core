`ifndef  SCRATCHPAD_BANK_IF_VH
`define SCRATCHPAD_BANK_IF_VH
`include "types_pkg.vh"

interface scratchpad_bank_if;
    import types_pkg::*;
    logic wFIFO_WEN, rFIFO_WEN, dramFIFO_REN, gemmFIFO_REN;
    logic [(BITS_PER_ROW+MAT_S_W+ROW_S_W):0] wFIFO_wdata;
    logic [(WORD_W+MAT_S_W+ROW_S_W+1):0] rFIFO_wdata;

    logic wFIFO_full, rFIFO_full, gemm_complete, dramFIFO_empty, gemmFIFO_empty, load_complete;
    logic [WORD_W+BITS_PER_ROW+MAT_S_W+ROW_S_W-1:0] dramFIFO_rdata;
    logic [BITS_PER_ROW+MAT_S_W+ROW_S_W+1:0] gemmFIFO_rdata;

    modport sp (
        input wFIFO_WEN, rFIFO_WEN, dramFIFO_REN, gemmFIFO_REN, wFIFO_wdata, rFIFO_wdata,
        output wFIFO_full, rFIFO_full, gemm_complete, dramFIFO_empty, gemmFIFO_empty, dramFIFO_rdata, gemmFIFO_rdata, load_complete
    );
    

endinterface

    /*
    in ports
    wFIFO_WEN
    wFIFO_wdata
    rFIFO_WEN
    rFIFO_wdata
    dramFIFO_REN
    gemmFIFO_REN

    out ports
    wFIFO_full
    rFIFO_full
    gemm_complete
    dramFIFO_rdata
    dramFIFO_empty
    gemmFIFO_rdata
    gemmFIFO_empty
    
    */

`endif 