import scpad_pkg::*;

module scpad_cntrl #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.sram_ctrl srif);

    sync_fifo #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_req_t))) wr_fifo (
        .clk(srif.clk),
        .rstn(srif.n_rst),
        .wr_en(srif.xbar_cntrl_req[IDX].valid),
        .din(srif.xbar_cntrl_req[IDX].write ? srif.xbar_cntrl_req[IDX] : '0),
        .rd_en(!{&spad_busy}),
        .dout(srif.cntrl_spad_req[IDX]),
        .full(srif.w_stall),
        .empty()
    );

    sync_fifo #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_req_t))) rd_fifo (
        .clk(srif.clk),
        .rstn(srif.n_rst),
        .wr_en(srif.head_stomach_req[IDX].valid),
        .din(!srif.xbar_cntrl_req[IDX].write ? srif.head_stomach_req[IDX] : '0),
        .rd_en(!{&spad_busy}),
        .dout(srif.cntrl_spad_req[IDX]),
        .full(srif.r_stall),
        .empty()
    );


endmodule