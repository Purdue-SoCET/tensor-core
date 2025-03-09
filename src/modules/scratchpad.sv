`include "load_FSM_if.vh"
`include "types_pkg.vh"
`include "scratchpad_if.vh"
`include "scratchpad_bank_if.vh"
`include "gemm_FSM_if.vh"
`include "dramstore_FSM_if.vh"

import types_pkg::*;

module scratchpad (
    input logic CLK, nRST,
    scratchpad_if.sp spif
);

    logic [2+MAT_S_W+ROW_S_W+WORD_W-1:0] instrFIFO_rdata;
    logic instrFIFO_empty, instrFIFO_REN;
    //logic [BITS_PER_ROW+ROW_S_W-1:0] psumoutFIFO_wdata;
    //logic psumoutFIFO_full, psumoutFIFO_WEN;  

    scratchpad_bank_if spbif0();
    scratchpad_bank_if spbif1();
    scratchpad_bank_if spbif2();
    scratchpad_bank_if spbif3();

    load_FSM_if lfsmif();

    gemm_FSM_if gfsmif();

    dramstore_FSM_if dfsmif();

    scratchpad_bank spb0(CLK, nRST, spbif0);
    scratchpad_bank spb1(CLK, nRST, spbif1);
    scratchpad_bank spb2(CLK, nRST, spbif2);
    scratchpad_bank spb3(CLK, nRST, spbif3);

    load_FSM loadFSM(CLK, nRST, lfsmif);

    gemm_FSM gemmFSM(CLK, nRST, gfsmif);

    dramstore_FSM dramstoreFSM(CLK, nRST, dfsmif);

    socetlib_fifo #(.T(logic [2+MAT_S_W+ROW_S_W+WORD_W-1:0]), .DEPTH(4)) instrFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(spif.instrFIFO_WEN), .REN(lfsmif.instrFIFO_REN), .clear(), .wdata(spif.instrFIFO_wdata), 
    .full(spif.instrFIFO_full), .empty(lfsmif.instrFIFO_empty), .underrun(), .overrun(), .count(), .rdata(lfsmif.instrFIFO_rdata));

    
    //PSUM OUT Logic
    assign lfsmif.psumoutFIFO_WEN = spif.psumout_en;
    assign lfsmif.psumoutFIFO_wdata = {spif.psumout_row_sel_in, spif.psumout_data}; /////FULL Not Implemented

    //Inputs
    assign gfsmif.drained = spif.drained;
    assign gfsmif.fifo_has_space = spif.fifo_has_space;
    assign lfsmif.load_data = spif.load_data;
    assign lfsmif.sLoad_hit = spif.sLoad_hit;
    assign lfsmif.sLoad_row = spif.sLoad_row;
    assign dfsmif.sStore_hit = spif.sStore_hit;

    //Outputs
    assign spif.gemm_complete = (spbif0.gemm_complete || spbif1.gemm_complete || spbif2.gemm_complete || spbif3.gemm_complete);
    assign spif.load_complete = (spbif0.load_complete || spbif1.load_complete || spbif2.load_complete || spbif3.load_complete);
    assign spif.partial_enable = gfsmif.partial_enable;
    assign spif.weight_enable = gfsmif.weight_enable;
    assign spif.input_enable = gfsmif.input_enable;
    assign spif.weight_input_data = gfsmif.weight_input_data;
    assign spif.partial_sum_data = gfsmif.partial_sum_data;
    assign spif.weight_input_row_sel = gfsmif.weight_input_row_sel;
    assign spif.partial_sum_row_sel = gfsmif.partial_sum_row_sel;
    assign spif.load_addr = lfsmif.load_addr;
    assign spif.sLoad = lfsmif.sLoad;
    assign spif.store_data = dfsmif.store_data;
    assign spif.store_addr = dfsmif.store_addr;
    assign spif.sStore = dfsmif.sStore;

    //LoadFSMs <-> Banks
    assign lfsmif.wFIFO0_full = spbif0.wFIFO_full;
    assign lfsmif.wFIFO1_full = spbif1.wFIFO_full;
    assign lfsmif.wFIFO2_full = spbif2.wFIFO_full;
    assign lfsmif.wFIFO3_full = spbif3.wFIFO_full;
    assign lfsmif.rFIFO0_full = spbif0.rFIFO_full;
    assign lfsmif.rFIFO1_full = spbif1.rFIFO_full;
    assign lfsmif.rFIFO2_full = spbif2.rFIFO_full;
    assign lfsmif.rFIFO3_full = spbif3.rFIFO_full;

    assign spbif0.wFIFO_wdata = lfsmif.wFIFO0_wdata;
    assign spbif1.wFIFO_wdata = lfsmif.wFIFO1_wdata;
    assign spbif2.wFIFO_wdata = lfsmif.wFIFO2_wdata;
    assign spbif3.wFIFO_wdata = lfsmif.wFIFO3_wdata;
    assign spbif0.rFIFO_wdata = lfsmif.rFIFO0_wdata;
    assign spbif1.rFIFO_wdata = lfsmif.rFIFO1_wdata;
    assign spbif2.rFIFO_wdata = lfsmif.rFIFO2_wdata;
    assign spbif3.rFIFO_wdata = lfsmif.rFIFO3_wdata;
    assign spbif0.wFIFO_WEN = lfsmif.wFIFO0_WEN;
    assign spbif1.wFIFO_WEN = lfsmif.wFIFO1_WEN;
    assign spbif2.wFIFO_WEN = lfsmif.wFIFO2_WEN;
    assign spbif3.wFIFO_WEN = lfsmif.wFIFO3_WEN;
    assign spbif0.rFIFO_WEN = lfsmif.rFIFO0_WEN;
    assign spbif1.rFIFO_WEN = lfsmif.rFIFO1_WEN;
    assign spbif2.rFIFO_WEN = lfsmif.rFIFO2_WEN;
    assign spbif3.rFIFO_WEN = lfsmif.rFIFO3_WEN;

    //LoadFSM <-> gemmFSM
    assign gfsmif.new_weight = lfsmif.new_weight;

    //DramStoreFSM <-> Banks
    assign dfsmif.dramFIFO0_empty = spbif0.dramFIFO_empty;
    assign dfsmif.dramFIFO1_empty = spbif1.dramFIFO_empty;
    assign dfsmif.dramFIFO2_empty = spbif2.dramFIFO_empty;
    assign dfsmif.dramFIFO3_empty = spbif3.dramFIFO_empty;
    assign dfsmif.dramFIFO0_rdata = spbif0.dramFIFO_rdata;
    assign dfsmif.dramFIFO1_rdata = spbif1.dramFIFO_rdata;
    assign dfsmif.dramFIFO2_rdata = spbif2.dramFIFO_rdata;
    assign dfsmif.dramFIFO3_rdata = spbif3.dramFIFO_rdata;

    assign spbif0.dramFIFO_REN = dfsmif.dramFIFO0_REN;
    assign spbif1.dramFIFO_REN = dfsmif.dramFIFO1_REN;
    assign spbif2.dramFIFO_REN = dfsmif.dramFIFO2_REN;
    assign spbif3.dramFIFO_REN = dfsmif.dramFIFO3_REN;

    //GEMMFSM <-> Banks
    assign gfsmif.gemmFIFO0_rdata = spbif0.gemmFIFO_rdata;
    assign gfsmif.gemmFIFO1_rdata = spbif1.gemmFIFO_rdata;
    assign gfsmif.gemmFIFO2_rdata = spbif2.gemmFIFO_rdata;
    assign gfsmif.gemmFIFO3_rdata = spbif3.gemmFIFO_rdata;
    assign gfsmif.gemmFIFO0_empty = spbif0.gemmFIFO_empty;
    assign gfsmif.gemmFIFO1_empty = spbif1.gemmFIFO_empty;
    assign gfsmif.gemmFIFO2_empty = spbif2.gemmFIFO_empty;
    assign gfsmif.gemmFIFO3_empty = spbif3.gemmFIFO_empty;

    assign spbif0.gemmFIFO_REN = gfsmif.gemmFIFO0_REN;
    assign spbif1.gemmFIFO_REN = gfsmif.gemmFIFO1_REN;
    assign spbif2.gemmFIFO_REN = gfsmif.gemmFIFO2_REN;
    assign spbif3.gemmFIFO_REN = gfsmif.gemmFIFO3_REN;



    /*
    {2'b(store?)(load?), 4'd(matrix_rd), 32,d(matrix address)} MATRIX LS
    {2'b11, 4'b(new weight?)000, 16'd0, 16'(gemm select)} GEMM Ops
    */

    /*
    Inputs:
    instrFIFO_WEN
    instrFIFO_wdata
    psumout_en
    psumout_row_sel_in
    psumout_data
    drained
    fifo_has_space
    load_data
    sLoad_hit
    sLoad_row
    sStore_hit

    Outputs:
    instrFIFO_full
    partial_enable
    weight_enable
    input_enable
    weight_input_data
    partial_sum_data
    weight_input_row_sel
    partial_sum_row_sel
    load_addr
    sLoad
    store_data
    store_addr
    sStore


    */

    
endmodule