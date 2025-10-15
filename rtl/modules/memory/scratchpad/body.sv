import scpad_pkg::*;

module body #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_body bif); 


    head #(.IDX(IDX)) head (.hif(bif));

    wxbar #(.IDX(IDX)) wxbar (.wif(bif));

    scpad_cntrl #(.IDX(IDX)) scpad_cntrl (.srif(bif));

    genvar gi;
    generate
        for (gi = 0; gi < NUM_COLS; gi++) begin : g_bank
            // SRAM_BANK is dual ported. 
            // But, we use it as single ported, because the workload doesn't demand it. 
            // the ren and wen are mutually exclusive.
            sram_bank #(.READ_LATENCY (2), .WRITE_LATENCY(2)) u_bank (
                .clk(bif.clk), .n_rst(bif.n_rst), .busy(bif.spad_busy[ti][gi]), 

                .ren(bif.cntrl_spad_req[ti].valid_mask[gi] && bif.cntrl_spad_req[ti].valid && !bif.cntrl_spad_req.write),
                .raddr(bif.cntrl_spad_req[ti].slot_mask[gi]),
                .rdone(bif.spad_cntrl_res[ti][gi]),
                .rdata(bif.spad_xbar_req.rdata[ti][gi]),

                .wen(bif.cntrl_spad_req[ti].xbar.valid_mask[gi] && bif.cntrl_spad_req[ti].valid && !bif.cntrl_spad_req.write),
                .waddr(bif.cntrl_spad_req[ti].xbar.slot_mask[gi]),
                .wdone(bif.spad_cntrl_res[ti][gi]),
                .wdata(bif.cntrl_spad_req[ti].wdata[gi])
            );
        end
    endgenerate

    rxbar #(.IDX(IDX)) rxbar (.wif(bif));

    tail #(.IDX(IDX)) tail (.tif(bif));

endmodule