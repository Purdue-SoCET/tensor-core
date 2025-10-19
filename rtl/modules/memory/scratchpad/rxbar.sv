/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_if.sv"

import scpad_pkg::*;

module rxbar #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.xbar_r rif); 

    typedef struct packed {
        logic valid;
        src_t src;
        slot_mask_t  slot_mask;
        mask_t  valid_mask;
    } pass_t;

    sync_fifo #(.DEPTH(XBAR_LATENCY), .DWIDTH($bits(pass_t))) pass_through_fifo (
        .clk(rif.clk), .rstn(rif.n_rst),
        .wr_en(!rif.r_stall[IDX]),
        .din(!rif.head_stomach_req[IDX].write ? {
            rif.spad_xbar_req[IDX].valid, 
            rif.spad_xbar_req[IDX].src,
            rif.spad_xbar_req[IDX].xbar.slot_mask, 
            rif.spad_xbar_req[IDX].xbar.valid_mask
            } : '0),
        .rd_en(!rif.r_stall[IDX]),
        .dout({
            rif.stomach_tail_res[IDX].valid, 
            rif.stomach_tail_res[IDX].src, 
            rif.stomach_tail_res[IDX].xbar.slot_mask, 
            rif.stomach_tail_res[IDX].xbar.valid_mask
            }),
        .full(),
        .empty()
    );

    xbar_if #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) rxbar_vif (.clk(rif.clk), .n_rst(rif.n_rst));

    always_comb begin 
        rxbar_vif.out = rif.stomach_tail_res[IDX].wdata;
        rxbar_vif.en = !rif.r_stall[IDX];
        for (int i = 0; i < NUM_COLS; i++) begin 
            rxbar_vif.in.din = !rif.head_stomach_req[IDX].write ? rif.spad_xbar_req[IDX].wdata[i] : '0;
            rxbar_vif.in.shift = rif.spad_xbar_req[IDX].xbar.shift_mask[i];
        end 
    end

    generate
        case (XBAR_TYPE)
            "NAIVE": naive_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) u_rxbar (rxbar_vif);
            "BENES": benes_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) u_rxbar (rxbar_vif);
            "BATCHER": batcher_xbar #(.SIZE(NUM_COLS), .DWIDTH(ELEM_BITS)) u_rxbar (rxbar_vif);
        endcase
    endgenerate

endmodule