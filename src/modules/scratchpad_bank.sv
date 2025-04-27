`include "sp_types_pkg.vh"
`include "scratchpad_bank_if.vh"
`include "sp_types_pkg.vh"
import sp_types_pkg::*;

module scratchpad_bank (
    input logic CLK, nRST,
    scratchpad_bank_if.sp spif
);


    logic [MATS_PER_BANK-1:0][3:0][BITS_PER_ROW-1:0] n_mats, mats;

    logic [BITS_PER_ROW-1:0] wdat, rdat;
    logic [MAT_S_W-1:0] w_mat_sel, r_mat_sel;
    logic [ROW_S_W-1:0] w_row_sel, r_row_sel;
    dramFIFO_t dramFIFO_wdata; 
    gemmFIFO_t gemmFIFO_wdata;
    logic wen, dramFIFO_WEN, dramFIFO_full, gemmFIFO_WEN, gemmFIFO_full;

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            mats <= '0;
        end
        else begin
            mats <= n_mats;
        end
    end

    always_comb begin
        n_mats = mats;
        if (wen) begin
            n_mats[w_mat_sel][w_row_sel] = wdat;
        end
    end

    assign rdat = mats[r_mat_sel][r_row_sel];

    
    always_comb begin
        {w_mat_sel, w_row_sel, wdat} = '0;
        wen = 1'b0;
        spif.gemm_complete = 1'b0;
        spif.load_complete = 1'b0;
        if (spif.wFIFO_WEN) begin
            w_mat_sel = spif.wFIFO_wdata.mat_s;
            w_row_sel = spif.wFIFO_wdata.row_s;
            wdat = spif.wFIFO_wdata.data;
            wen = 1'b1;
            if (spif.wFIFO_wdata.gemm_result) begin
                if (spif.wFIFO_wdata.row_s == 2'd3) begin
                    spif.gemm_complete = 1'b1;
                end
            end
            else begin
                if (spif.wFIFO_wdata.row_s == 2'd3) begin
                    spif.load_complete = 1'b1;
                end
            end
        end
    end

    always_comb begin
        {r_mat_sel, r_row_sel} = '0;
        dramFIFO_WEN = 1'b0;
        gemmFIFO_WEN = 1'b0;
        dramFIFO_wdata = '0;
        gemmFIFO_wdata = '0;
        if (spif.rFIFO_WEN) begin
            if (spif.rFIFO_wdata.mat_t == '0) begin
                if (dramFIFO_full == 1'b0) begin
                    r_mat_sel = spif.rFIFO_wdata.mat_s;
                    r_row_sel = spif.rFIFO_wdata.row_s;
                    dramFIFO_WEN = 1'b1;
                    dramFIFO_wdata.addr = spif.rFIFO_wdata.addr;
                    dramFIFO_wdata.mat_s = spif.rFIFO_wdata.mat_s;
                    dramFIFO_wdata.row_s = spif.rFIFO_wdata.row_s;
                    dramFIFO_wdata.data = rdat;
                end
            end
            else begin
                if (gemmFIFO_full == 1'b0) begin
                    r_mat_sel = spif.rFIFO_wdata.mat_s;
                    r_row_sel = spif.rFIFO_wdata.row_s;
                    gemmFIFO_WEN = 1'b1;
                    gemmFIFO_wdata.mat_t = spif.rFIFO_wdata.mat_t;
                    gemmFIFO_wdata.mat_s = spif.rFIFO_wdata.mat_s;
                    gemmFIFO_wdata.row_s = spif.rFIFO_wdata.row_s;
                    gemmFIFO_wdata.data = rdat;
                end
            end
        end
    end

    socetlib_fifo #(.T(dramFIFO_t), .DEPTH(4)) dramFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(dramFIFO_WEN), .REN(spif.dramFIFO_REN), .clear(), .wdata(dramFIFO_wdata), 
    .full(dramFIFO_full), .empty(spif.dramFIFO_empty), .underrun(), .overrun(), .count(), .rdata(spif.dramFIFO_rdata));

    socetlib_fifo #(.T(gemmFIFO_t), .DEPTH(8)) gemmFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(gemmFIFO_WEN), .REN(spif.gemmFIFO_REN), .clear(), .wdata(gemmFIFO_wdata), 
    .full(gemmFIFO_full), .empty(spif.gemmFIFO_empty), .underrun(), .overrun(), .count(), .rdata(spif.gemmFIFO_rdata));
    
endmodule
