`ifndef  SCRATCHPAD_BANK_IF_VH
`define SCRATCHPAD_BANK_IF_VH
`include "sp_types_pkg.vh"

interface scratchpad_bank_if;
    import sp_types_pkg::*;
    logic wFIFO_WEN, rFIFO_WEN, dramFIFO_REN, gemmFIFO_REN;
    wFIFO_t wFIFO_wdata;
    rFIFO_t rFIFO_wdata;

    logic wFIFO_full, rFIFO_full, gemm_complete, dramFIFO_empty, gemmFIFO_empty, load_complete;
    dramFIFO_t dramFIFO_rdata;
    gemmFIFO_t gemmFIFO_rdata;

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