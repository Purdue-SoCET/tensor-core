`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module body #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.spad_body bif
); 
    import scpad_types_pkg::*;

    mask_t busy [NUM_SCPADS]; 

    head #(.IDX(IDX)) u_head (.clk(clk), .n_rst(n_rst), .hif(bif));

    wxbar #(.IDX(IDX)) u_write_xbar_ti (.clk(clk), .n_rst(n_rst), .wif(bif));

    spad_cntrl #(.IDX(IDX)) u_sram_controller u_spad_cntrl (.clk(clk), .n_rst(n_rst), .srif(bif));

    genvar gi;
    generate
        for (gi = 0; gi < NUM_COLS; gi++) begin : g_bank
            sram_bank #(.READ_LATENCY (2), .WRITE_LATENCY(2)) u_bank (
                .clk(clk), .n_rst(n_rst), .busy(busy[ti][gi]), 

                .ren(bif.cntrl_spad_rd_req[ti].valid_mask[gi] && bif.cntrl_spad_rd_req[ti].valid),
                .raddr((bif.cntrl_spad_rd_req[ti].slot_mask[gi]),
                .rdone(bif.spad_cntrl_rd_res[ti][gi]),
                .rdata(bif.spad_xbar_rd_req.rdata[ti][gi]),

                .wen(bif.cntrl_spad_wr_req[ti].xbar.valid_mask[gi] && bif.cntrl_spad_wr_req[ti].valid),
                .waddr(bif.cntrl_spad_wr_req[ti].xbar.slot_mask[gi]),
                .wdone(bif.spad_cntrl_wr_res[ti]),
                .wdata(bif.cntrl_spad_wr_req[ti].wdata[gi])
            );
        end
    endgenerate

    rxbar #(.IDX(IDX)) u_write_xbar_ti (.clk(clk), .n_rst(n_rst), .wif(bif));

    tail #(.IDX(IDX)) u_tail (.clk(clk), .n_rst(n_rst), .tif(bif));

endmodule