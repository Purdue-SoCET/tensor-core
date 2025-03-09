/*
    Interface signals for the Matrix Load Store
*/
`ifndef FU_MATRIX_LS_IF_VH
`define FU_MATRIX_LS_IF_VH

// types
`include "datapath_types.vh"
`include "isa_types.vh"

interface fu_matrix_ls_if;
// import types
import datapath_pkg::*;
import isa_pkg::*;

// Signals

/*
    Inputs: 
    enable: From issue queue
    ls_in: Load or Store
    rd_in: destination reg
    rs_in: source reg
    stride_in: stride
    imm_in   : immediate
    mhit: Scratchpad ready
*/

logic           mhit;
logic           enable;
regbits_t       rd_in;
word_t          rs_in;
word_t          imm_in;
word_t          stride_in;

// Outputs (REFER TO DATAPATH_TYPES)
matrix_mem_t fu_matls_in;
matrix_ls_t fu_matls_out;

// LS Matrix Port Map
modport mls (
    input   mhit, enable, rd_in, rs_in, stride_in, imm_in, fu_matls_in,
    output  fu_matls_out
);

modport tb (
    output   mhit, enable, rd_in, rs_in, stride_in, imm_in, fu_matls_in,
    input  fu_matls_out
);

endinterface

`endif //FU_MATRIX_LS_IF_VH
