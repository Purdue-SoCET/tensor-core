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
logic [1:0]     ls_in;
logic [3:0]     rd_in, rs_in;
logic [10:0]    imm_in;
word_t          stride_in;

// Outputs (REFER TO DATAPATH_TYPES)
matrix_ls_t fu_matls_out;

// LS Matrix Port Map
modport mls (
    input   mhit, enable, ls_in, rd_in, rs_in, stride_in, imm_in,
    output  fu_matls_out
);

modport tb (
    output   mhit, enable, ls_in, rd_in, rs_in, stride_in, imm_in,
    input  fu_matls_out
);

endinterface

`endif //FU_MATRIX_LS_IF_VH
