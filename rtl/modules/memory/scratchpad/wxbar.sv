/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_if.sv"

import scpad_pkg::*;

module wxbar #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.xbar_w wif); 

    typedef struct packed {
        logic valid;
        src_t src;
        slot_mask_t  slot_mask;
        mask_t valid_mask;
    } pass_t;

    sync_fifo #(.DEPTH(XBAR_LATENCY), .DWIDTH($bits(pass_t))) pass_through_fifo (
        .clk(wif.clk), .rstn(wif.n_rst),
        .wr_en(!rif.w_stall[IDX]),
        .din(rif.head_stomach_req[IDX].write ? {
                rif.head_stomach_req[IDX].valid, 
                rif.head_stomach_req[IDX].src, 
                rif.head_stomach_req[IDX].xbar.slot_mask, 
                rif.head_stomach_req[IDX].xbar.valid_mask
            } : '0),
        .rd_en(!rif.w_stall[IDX]),
        .dout({
                rif.xbar_cntrl_req[IDX].valid, 
                rif.xbar_cntrl_req[IDX].src, 
                rif.xbar_cntrl_req[IDX].xbar.slot_mask, 
                rif.xbar_cntrl_req[IDX].xbar.valid_mask
            }),
        .full(),
        .empty()
    );


    xbar_if #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) wxbar_vif (
        .clk(wif.clk), .n_rst(wif.n_rst),
        .en(!rif.w_stall[IDX]), 
        .din(rif.head_stomach_req[IDX].write ? rif.head_stomach_req[IDX].wdata : '0),
        .shift(rif.head_stomach_req[IDX].xbar.shift_mask),
        .dout(rif.xbar_cntrl_req[IDX].wdata)
    );

    generate
        case (XBAR_TYPE)
            "NAIVE": naive_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) u_wxbar (wxbar_vif);
            "BENES": benes_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) u_wxbar (wxbar_vif);
            "BATCHER": batcher_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) u_wxbar (wxbar_vif);
        endcase
    endgenerate

endmodule