`ifndef  SCRATCHPAD_BANK_IF_VH
`define SCRATCHPAD_BANK_IF_VH
`include "types_pkg.vh"

interface scratchpad_bank_if;
    import types_pkg::*;
    row_bits_t wdat, rdat;
    mat_s_t w_mat_sel, r_mat_sel;
    row_s_t w_row_sel, r_row_sel;

    modport sp (
        input wdat, w_mat_sel, w_row_sel, wen, r_mat_sel, r_row_sel
        output rdat
    );
    

endinterface

`endif 