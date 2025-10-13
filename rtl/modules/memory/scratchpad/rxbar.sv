`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module rxbar #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.xbar_r wif
); 
    import scpad_types_pkg::*;

    typedef struct packed {
        logic valid;
        src_t src;
        slot_mask_t  slot_mask;
        mask_t  valid_mask;
    } rd_pass_t;

    sync_fifo #(.DEPTH(XBAR_LATENCY), .DWIDTH($bits(rd_pass_t))) pass_through_fifo (
        .clk(clk),
        .rstn(n_rst),
        .wr_en(!rif.r_stall[IDX]),
        .din({rif.spad_xbar_rd_req[IDX].valid, rif.spad_xbar_rd_req[IDX].src, rif.spad_xbar_rd_req[IDX].xbar.slot_mask, rif.spad_xbar_rd_req[IDX].xbar.valid_mask}),
        .rd_en(!rif.r_stall[IDX]),
        .dout({rif.stomach_tail_rd_res[IDX].valid, rif.stomach_tail_rd_res[IDX].src, rif.stomach_tail_rd_res[IDX].xbar.slot_mask, rif.stomach_tail_rd_res[IDX].xbar.valid_mask}),
        .full(),
        .empty()
    );

    generate
        unique case (MODE)
            "NAIVE": naive_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS) u_wxbar (
                    .clk(clk), .n_rst(n_rst), 
                    .en(!rif.r_stall[IDX]), // enables the entire pipe. stalls all stages 
                    .din(rif.spad_xbar_rd_req[IDX].wdata), 
                    .shift(rif.spad_xbar_rd_req[IDX].xbar.shift_mask), 
                    .dout(rif.stomach_tail_rd_res[IDX].wdata)
                );
            "BENES": benes_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS) u_wxbar (
                    .clk(clk), .n_rst(n_rst), 
                    .en(!rif.r_stall[IDX]), 
                    .din(rif.spad_xbar_rd_req[IDX].wdata), 
                    .shift(rif.spad_xbar_rd_req[IDX].xbar.shift_mask), 
                    .dout(rif.stomach_tail_rd_res[IDX].wdata)
                );
            "BATCHER": batcher_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS) u_wxbar (
                    .clk(clk), .n_rst(n_rst), 
                    .en(!rif.r_stall[IDX]),
                    .din(rif.spad_xbar_rd_req[IDX].wdata), 
                    .shift(rif.spad_xbar_rd_req[IDX].xbar.shift_mask), 
                    .dout(rif.stomach_tail_rd_res[IDX].wdata)
                );
        endcase
    endgenerate

endmodule