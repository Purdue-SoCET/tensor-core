`ifndef  SOCETLIB_FIFO_IF_VH
`define SOCETLIB_FIFO_IF_VH
`include "types_pkg.vh"

interface socetlib_fifo_if;
    import types_pkg::*;
    
    parameter type T = logic [7:0];
    parameter DEPTH = 8;

    logic WEN;
    logic REN;
    logic clear;
    logic T wdata;
    output logic full,
    output logic empty,
    output logic underrun, 
    output logic overrun,
    output logic [$clog2(DEPTH+1)-1:0] count,
    output T rdata

    modport sp (
        input wdat, w_mat_sel, w_row_sel, wen
        output rdat, r_mat_sel, r_row_sel
    );
    

endinterface

`endif 