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
    wFIFO_t wFIFO_rdata;
    rFIFO_t rFIFO_rdata;
    dramFIFO_t dramFIFO_wdata; 
    gemmFIFO_t gemmFIFO_wdata;
    logic wFIFO_REN, wFIFO_empty, wen, rFIFO_empty, rFIFO_REN, dramFIFO_WEN, dramFIFO_full, gemmFIFO_WEN, gemmFIFO_full;

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
        wFIFO_REN = 1'b0;
        spif.gemm_complete = 1'b0;
        spif.load_complete = 1'b0;
        if (wFIFO_empty == 1'b0) begin
            w_mat_sel = wFIFO_rdata.mat_s;
            w_row_sel = wFIFO_rdata.row_s;
            wdat = wFIFO_rdata.data;
            wen = 1'b1;
            wFIFO_REN = 1'b1;
            if (wFIFO_rdata.gemm_result) begin
                if (wFIFO_rdata.row_s == 2'd3) begin
                    spif.gemm_complete = 1'b1;
                end
            end
            else begin
                if (wFIFO_rdata.row_s == 2'd3) begin
                    spif.load_complete = 1'b1;
                end
            end
        end
    end

    always_comb begin
        {r_mat_sel, r_row_sel} = '0;
        rFIFO_REN = 1'b0;
        dramFIFO_WEN = 1'b0;
        gemmFIFO_WEN = 1'b0;
        dramFIFO_wdata = '0;
        gemmFIFO_wdata = '0;
        if (rFIFO_empty == 1'b0) begin
            if (rFIFO_rdata.mat_t == '0) begin
                if (dramFIFO_full == 1'b0) begin
                    r_mat_sel = rFIFO_rdata.mat_s;
                    r_row_sel = rFIFO_rdata.row_s;
                    rFIFO_REN = 1'b1;
                    dramFIFO_WEN = 1'b1;
                    dramFIFO_wdata.addr = rFIFO_rdata.addr;
                    dramFIFO_wdata.mat_s = rFIFO_rdata.mat_s;
                    dramFIFO_wdata.row_s = rFIFO_rdata.row_s;
                    dramFIFO_wdata.data = rdat;
                end
            end
            else begin
                if (gemmFIFO_full == 1'b0) begin
                    r_mat_sel = rFIFO_rdata.mat_s;
                    r_row_sel = rFIFO_rdata.row_s;
                    rFIFO_REN = 1'b1;
                    gemmFIFO_WEN = 1'b1;
                    gemmFIFO_wdata.mat_t = rFIFO_rdata.mat_t;
                    gemmFIFO_wdata.mat_s = rFIFO_rdata.mat_s;
                    gemmFIFO_wdata.row_s = rFIFO_rdata.row_s;
                    gemmFIFO_wdata.data = rdat;
                end
            end
        end
    end


    //{1 bit gemm result, 2 bits mat sel, 2 bits row sel, 64 bits data}
    socetlib_fifo #(.T(wFIFO_t), .DEPTH(2)) wFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(spif.wFIFO_WEN), .REN(wFIFO_REN), .clear(), .wdata(spif.wFIFO_wdata), 
    .full(spif.wFIFO_full), .empty(wFIFO_empty), .underrun(), .overrun(), .count(), .rdata(wFIFO_rdata));

    //{2(32'baddress, 00 = store, rest = gemm mat type (order preserved)), 2 bits mat sel, 2 bits row sel,}
    socetlib_fifo #(.T(rFIFO_t), .DEPTH(2)) rFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(spif.rFIFO_WEN), .REN(rFIFO_REN), .clear(), .wdata(spif.rFIFO_wdata), 
    .full(spif.rFIFO_full), .empty(rFIFO_empty), .underrun(), .overrun(), .count(), .rdata(rFIFO_rdata));

    //{32'baddress, 2 bits mat_sel, 2 bits row sel, 64 bits data}
    socetlib_fifo #(.T(dramFIFO_t), .DEPTH(8)) dramFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(dramFIFO_WEN), .REN(spif.dramFIFO_REN), .clear(), .wdata(dramFIFO_wdata), 
    .full(dramFIFO_full), .empty(spif.dramFIFO_empty), .underrun(), .overrun(), .count(), .rdata(spif.dramFIFO_rdata));

    //{2 bits gemm mat type, 2 bits mat_sel, 2 bits row sel, 64 bits data}
    socetlib_fifo #(.T(gemmFIFO_t), .DEPTH(8)) gemmFIFO(.CLK(CLK), 
    .nRST(nRST), .WEN(gemmFIFO_WEN), .REN(spif.gemmFIFO_REN), .clear(), .wdata(gemmFIFO_wdata), 
    .full(gemmFIFO_full), .empty(spif.gemmFIFO_empty), .underrun(), .overrun(), .count(), .rdata(spif.gemmFIFO_rdata));

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

    
endmodule
