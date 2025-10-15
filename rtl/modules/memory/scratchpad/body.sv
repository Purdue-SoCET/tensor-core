import scpad_pkg::*;

module body #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_body bif); 


    head #(.IDX(IDX)) head (.hif(bif));

    wxbar #(.IDX(IDX)) wxbar (.wif(bif));

    scpad_cntrl #(.IDX(IDX)) scpad_cntrl (.srif(bif));

    genvar gi;
    generate
        for (gi = 0; gi < NUM_COLS; gi++) begin : g_bank
            sram_bank #(.READ_LATENCY (2), .WRITE_LATENCY(2)) u_bank (
                .clk(bif.clk), .n_rst(bif.n_rst), .busy(bif.sram_busy[ti][gi]), 

                .ren(bif.cntrl_spad_rd_req[ti].valid_mask[gi] && bif.cntrl_spad_rd_req[ti].valid),
                .raddr(bif.cntrl_spad_rd_req[ti].slot_mask[gi]),
                .rdone(bif.spad_cntrl_rd_res[ti][gi]),
                .rdata(bif.spad_xbar_rd_req.rdata[ti][gi]),

                .wen(bif.cntrl_spad_wr_req[ti].xbar.valid_mask[gi] && bif.cntrl_spad_wr_req[ti].valid),
                .waddr(bif.cntrl_spad_wr_req[ti].xbar.slot_mask[gi]),
                .wdone(bif.spad_cntrl_wr_res[ti]),
                .wdata(bif.cntrl_spad_wr_req[ti].wdata[gi])
            );
        end
    endgenerate

    rxbar #(.IDX(IDX)) rxbar (.wif(bif));

    tail #(.IDX(IDX)) tail (.tif(bif));

endmodule