import scpad_pkg::*;

module scpad_cntrl #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.sram_ctrl srif);

    sync_fifo #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_wr_req_t))) wr_fifo (
        .clk(srif.clk),
        .rstn(srif.n_rst),
        .wr_en(srif.xbar_cntrl_wr_req[IDX].valid && srif.xbar_cntrl_wr_req[IDX].xbar.valid_mask),
        .din(srif.xbar_cntrl_wr_req[IDX]),
        .rd_en(!{&sram_busy}),
        .dout(srif.cntrl_spad_wr_req[IDX]),
        .full(srif.w_stall),
        .empty()
    );

    sync_fifo #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_rd_req_t))) rd_fifo (
        .clk(srif.clk),
        .rstn(srif.n_rst),
        .wr_en(srif.head_stomach_rd_req[IDX].valid && srif.head_stomach_rd_req[IDX].xbar.valid_mask),
        .din(srif.head_stomach_rd_req[IDX]),
        .rd_en(!{&sram_busy}),
        .dout(srif.cntrl_spad_rd_req[IDX]),
        .full(srif.r_stall),
        .empty()
    );


endmodule