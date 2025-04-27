`include "sp_types_pkg.vh"
`include "scratchpad_if.vh"
`include "scratchpad_bank_if.vh"
`include "gemm_FSM_if.vh"
`include "dramstore_FSM_if.vh"
`include "bank_access_FSM_if.vh"

import sp_types_pkg::*;

module scratchpad (
    input logic CLK, nRST,
    scratchpad_if.sp spif
);

    instrFIFO_t prev_instrFIFO_rdata, instrFIFO_rdata;
    logic instrFIFO_empty, instrFIFO_REN, instrFIFO_unused, n_instrFIFO_unused, psumoutFIFO_REN, psumoutFIFO_empty, psumoutFIFO_full, new_instr;
    psumoutFIFO_t psumoutFIFO_rdata, psumoutFIFO_wdata;
    logic [MAT_S_W+2-1:0] gemm_mat, n_gemm_mat;
    logic [1:0] count;

    scratchpad_bank_if spbif0();
    scratchpad_bank_if spbif1();
    scratchpad_bank_if spbif2();
    scratchpad_bank_if spbif3();

    bank_access_FSM_if bfsmif0();
    bank_access_FSM_if bfsmif1();
    bank_access_FSM_if bfsmif2();
    bank_access_FSM_if bfsmif3();

    gemm_FSM_if gfsmif();

    dramstore_FSM_if dfsmif();

    scratchpad_bank spb0(CLK, nRST, spbif0);
    scratchpad_bank spb1(CLK, nRST, spbif1);
    scratchpad_bank spb2(CLK, nRST, spbif2);
    scratchpad_bank spb3(CLK, nRST, spbif3);

    bank_access_FSM #(.BANK_NUM(0)) bfsm0(CLK, nRST, bfsmif0);
    bank_access_FSM #(.BANK_NUM(1)) bfsm1(CLK, nRST, bfsmif1);
    bank_access_FSM #(.BANK_NUM(2)) bfsm2(CLK, nRST, bfsmif2);
    bank_access_FSM #(.BANK_NUM(3)) bfsm3(CLK, nRST, bfsmif3);

    gemm_FSM gemmFSM(CLK, nRST, gfsmif);

    dramstore_FSM dramstoreFSM(CLK, nRST, dfsmif);

    socetlib_fifo #(.T(instrFIFO_t), .DEPTH(4)) instrFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(spif.instrFIFO_WEN), .REN(instrFIFO_REN), .clear(), .wdata(spif.instrFIFO_wdata), 
    .full(spif.instrFIFO_full), .empty(instrFIFO_empty), .underrun(), .overrun(), .count(count), .rdata(instrFIFO_rdata));

    socetlib_fifo #(.T(psumoutFIFO_t), .DEPTH(4)) psumoutFIFO (.CLK(CLK), 
    .nRST(nRST), .WEN(spif.psumout_en), .REN(psumoutFIFO_REN), .clear(), .wdata(psumoutFIFO_wdata), 
    .full(psumoutFIFO_full), .empty(psumoutFIFO_empty), .underrun(), .overrun(), .count(), .rdata(psumoutFIFO_rdata));
    
    //PSUM OUT Logic
    assign psumoutFIFO_REN = bfsmif0.psumoutFIFO_REN || bfsmif1.psumoutFIFO_REN || bfsmif2.psumoutFIFO_REN || bfsmif3.psumoutFIFO_REN;
    assign psumoutFIFO_wdata.row_s = spif.psumout_row_sel_in;
    assign psumoutFIFO_wdata.data = spif.psumout_data;

    //Inputs
    assign gfsmif.drained = spif.drained;
    assign gfsmif.fifo_has_space = spif.fifo_has_space;
    assign bfsmif0.load_data = spif.load_data;
    assign bfsmif1.load_data = spif.load_data;
    assign bfsmif2.load_data = spif.load_data;
    assign bfsmif3.load_data = spif.load_data;
    assign bfsmif0.sLoad_hit = spif.sLoad_hit;
    assign bfsmif1.sLoad_hit = spif.sLoad_hit;
    assign bfsmif2.sLoad_hit = spif.sLoad_hit;
    assign bfsmif3.sLoad_hit = spif.sLoad_hit;
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
    assign spif.sLoad = (bfsmif0.sLoad || bfsmif1.sLoad || bfsmif2.sLoad || bfsmif3.sLoad);
    always_comb begin
        spif.load_addr = '0;
        if (bfsmif0.sLoad) begin
            spif.load_addr = bfsmif0.load_addr;
        end
        else if (bfsmif1.sLoad) begin
            spif.load_addr = bfsmif1.load_addr;
        end
        else if (bfsmif2.sLoad) begin
            spif.load_addr = bfsmif2.load_addr;
        end
        else if (bfsmif3.sLoad) begin
            spif.load_addr = bfsmif3.load_addr;
        end
    end
    assign spif.store_data = dfsmif.store_data;
    assign spif.store_addr = dfsmif.store_addr;
    assign spif.sStore = dfsmif.sStore;
    assign spif.store_complete = dfsmif.store_complete;

    //LoadFSMs <-> Banks
    assign bfsmif0.wFIFO_full = spbif0.wFIFO_full;
    assign bfsmif1.wFIFO_full = spbif1.wFIFO_full;
    assign bfsmif2.wFIFO_full = spbif2.wFIFO_full;
    assign bfsmif3.wFIFO_full = spbif3.wFIFO_full;
    assign bfsmif0.rFIFO_full = spbif0.rFIFO_full;
    assign bfsmif1.rFIFO_full = spbif1.rFIFO_full;
    assign bfsmif2.rFIFO_full = spbif2.rFIFO_full;
    assign bfsmif3.rFIFO_full = spbif3.rFIFO_full;

    assign spbif0.wFIFO_wdata = bfsmif0.wFIFO_wdata;
    assign spbif1.wFIFO_wdata = bfsmif1.wFIFO_wdata;
    assign spbif2.wFIFO_wdata = bfsmif2.wFIFO_wdata;
    assign spbif3.wFIFO_wdata = bfsmif3.wFIFO_wdata;
    assign spbif0.rFIFO_wdata = bfsmif0.rFIFO_wdata;
    assign spbif1.rFIFO_wdata = bfsmif1.rFIFO_wdata;
    assign spbif2.rFIFO_wdata = bfsmif2.rFIFO_wdata;
    assign spbif3.rFIFO_wdata = bfsmif3.rFIFO_wdata;
    assign spbif0.wFIFO_WEN = bfsmif0.wFIFO_WEN;
    assign spbif1.wFIFO_WEN = bfsmif1.wFIFO_WEN;
    assign spbif2.wFIFO_WEN = bfsmif2.wFIFO_WEN;
    assign spbif3.wFIFO_WEN = bfsmif3.wFIFO_WEN;
    assign spbif0.rFIFO_WEN = bfsmif0.rFIFO_WEN;
    assign spbif1.rFIFO_WEN = bfsmif1.rFIFO_WEN;
    assign spbif2.rFIFO_WEN = bfsmif2.rFIFO_WEN;
    assign spbif3.rFIFO_WEN = bfsmif3.rFIFO_WEN;

    //LoadFSM <-> gemmFSM
    assign gfsmif.new_weight = instrFIFO_rdata.ls_matrix_rd_gemm_new_weight[5] && new_instr && (instrFIFO_rdata.opcode == 2'd3);

    //LoadFSMIN
    assign bfsmif0.instrFIFO_empty = instrFIFO_empty;
    assign bfsmif1.instrFIFO_empty = instrFIFO_empty;
    assign bfsmif2.instrFIFO_empty = instrFIFO_empty;
    assign bfsmif3.instrFIFO_empty = instrFIFO_empty;
    assign bfsmif0.psumoutFIFO_full = psumoutFIFO_full;
    assign bfsmif1.psumoutFIFO_full = psumoutFIFO_full;
    assign bfsmif2.psumoutFIFO_full = psumoutFIFO_full;
    assign bfsmif3.psumoutFIFO_full = psumoutFIFO_full;
    assign bfsmif0.instrFIFO_rdata = instrFIFO_rdata;
    assign bfsmif1.instrFIFO_rdata = instrFIFO_rdata;
    assign bfsmif2.instrFIFO_rdata = instrFIFO_rdata;
    assign bfsmif3.instrFIFO_rdata = instrFIFO_rdata;
    assign bfsmif0.psumoutFIFO_rdata = psumoutFIFO_rdata;
    assign bfsmif1.psumoutFIFO_rdata = psumoutFIFO_rdata;
    assign bfsmif2.psumoutFIFO_rdata = psumoutFIFO_rdata;
    assign bfsmif3.psumoutFIFO_rdata = psumoutFIFO_rdata;
    assign bfsmif0.new_instr = new_instr;
    assign bfsmif1.new_instr = new_instr;
    assign bfsmif2.new_instr = new_instr;
    assign bfsmif3.new_instr = new_instr;
    assign bfsmif0.gemm_mat = gemm_mat;
    assign bfsmif1.gemm_mat = gemm_mat;
    assign bfsmif2.gemm_mat = gemm_mat;
    assign bfsmif3.gemm_mat = gemm_mat;
    assign new_instr = (prev_instrFIFO_rdata.opcode != instrFIFO_rdata.opcode) && (instrFIFO_rdata.opcode != '0);
    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            gemm_mat <= '0;
            instrFIFO_unused <= 1'b1;
            prev_instrFIFO_rdata <= '0;
        end
        else begin
            gemm_mat <= n_gemm_mat;
            instrFIFO_unused <= n_instrFIFO_unused;
            prev_instrFIFO_rdata <= instrFIFO_rdata;
        end
    end
    always_comb begin
        n_gemm_mat = gemm_mat;
        n_instrFIFO_unused = instrFIFO_unused;
        if ((instrFIFO_rdata.opcode == 2'd3) && new_instr) begin
            n_gemm_mat = instrFIFO_rdata.ls_addr_gemm_gemm_sel[23:18];
        end
        if (spif.instrFIFO_WEN) begin
            n_instrFIFO_unused = 1'b0;
        end
    end


    //LoadFSMOut
    assign instrFIFO_REN = bfsmif0.instrFIFO_REN & bfsmif1.instrFIFO_REN & bfsmif2.instrFIFO_REN & bfsmif3.instrFIFO_REN;

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
    
endmodule