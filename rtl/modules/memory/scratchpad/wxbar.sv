`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module wxbar #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.xbar_w wif
); 
    import scpad_types_pkg::*;

    typedef struct packed {
        logic valid;
        src_t src;
        slot_mask_t  slot_mask;
        mask_t  valid_mask;
    } wr_pass_t;

    sync_fifo #(.DEPTH(XBAR_LATENCY), .DWIDTH($bits(wr_pass_t))) pass_through_fifo (
        .clk(clk),
        .rstn(n_rst),
        .wr_en(!rif.w_stall[IDX]),
        .din({rif.head_stomach_wr_req[IDX].valid, rif.head_stomach_wr_req[IDX].src, rif.head_stomach_wr_req[IDX].xbar.slot_mask, rif.head_stomach_wr_req[IDX].xbar.valid_mask}),
        .rd_en(!rif.w_stall[IDX]),
        .dout({rif.xbar_cntrl_wr_req[IDX].valid, rif.xbar_cntrl_wr_req[IDX].src, rif.xbar_cntrl_wr_req[IDX].xbar.slot_mask, rif.xbar_cntrl_wr_req[IDX].xbar.valid_mask}),
        .full(),
        .empty()
    );

    generate
        unique case (MODE)
            "NAIVE": naive_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS) u_wxbar (
                    .clk(clk), .n_rst(n_rst), 
                    .en(!rif.w_stall[IDX]), // enables the entire pipe. stalls all stages 
                    .din(rif.head_stomach_wr_req[IDX].wdata), 
                    .shift(rif.head_stomach_wr_req[IDX].xbar.shift_mask), 
                    .dout(rif.xbar_cntrl_wr_req[IDX].wdata)
                );
            "BENES": benes_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS) u_wxbar (
                    .clk(clk), .n_rst(n_rst), 
                    .en(!rif.w_stall[IDX]), 
                    .din(rif.head_stomach_wr_req[IDX].wdata), 
                    .shift(rif.head_stomach_wr_req[IDX].xbar.shift_mask), 
                    .dout(rif.xbar_cntrl_wr_req[IDX].wdata)
                );
            "BATCHER": batcher_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS) u_wxbar (
                    .clk(clk), .n_rst(n_rst), 
                    .en(!rif.w_stall[IDX]),
                    .din(rif.head_stomach_wr_req[IDX].wdata), 
                    .shift(rif.head_stomach_wr_req[IDX].xbar.shift_mask), 
                    .dout(rif.xbar_cntrl_wr_req[IDX].wdata)
                );
        endcase
    endgenerate

endmodule