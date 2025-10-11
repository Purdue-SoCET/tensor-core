`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module sram_cntrl  #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input  logic clk, n_rst,
    scpad_if.sram_ctrl srif,
);
    import scpad_types_pkg::*;

    sync_fifo u_wr_fifo_ti #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_wr_req_t))) u_fifo_wr_ti (
        .clk(clk),
        .rstn(n_rst),
        .wr_en(srif.xbar_cntrl_wr_req[IDX].valid && srif.xbar_cntrl_wr_req[IDX].xbar.valid_mask),
        .din(srif.xbar_cntrl_wr_req[IDX]),
        .rd_en(!{&busy}),
        .dout(srif.cntrl_spad_wr_req[IDX]),
        .full(srif.w_stall),
        .empty()
    );

    sync_fifo u_rd_fifo_ti #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_rd_req_t))) u_fifo_rd_ti (
        .clk(clk),
        .rstn(n_rst),
        .wr_en(srif.head_stomach_rd_req[IDX].valid && srif.head_stomach_rd_req[IDX].xbar.valid_mask),
        .din(srif.head_stomach_rd_req[IDX]),
        .rd_en(!{&busy}),
        .dout(srif.cntrl_spad_rd_req[IDX]),
        .full(srif.r_stall),
        .empty()
    );


endmodule