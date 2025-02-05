`ifndef  OUTFIFO_FSM_IF_VH
`define OUTFIFO_FSM_IF_VH
`include "types_pkg.vh"

interface outFIFO_FSM_if;
    import types_pkg::*;

    logic instr_FIFO_empty, instr_FIFO_REN;
    mat_s_t r_mat_sel_1, r_mat_sel_2, r_mat_sel_3, r_mat_sel_4;
    row_s_t r_row_sel_1, r_row_sel_2, r_row_sel_3, r_row_sel_4;

    modport sp (
        input instr_FIFO_empty, 
        output instr_FIFO_REN, r_mat_sel_1, r_row_sel_1, r_mat_sel_2, r_row_sel_2, r_mat_sel_3, r_row_sel_3, r_mat_sel_4, r_row_sel_4
    );
    

endinterface

`endif 