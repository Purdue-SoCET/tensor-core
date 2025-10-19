/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "scpad_pkg.sv"
`include "scpad_if.sv"
import scpad_pkg::*;

module body #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_body bif); 

    head #(.IDX(IDX)) head (.hif(bif));

    wxbar #(.IDX(IDX)) wxbar (.wif(bif));

    scpad_cntrl #(.IDX(IDX)) scpad_cntrl (.srif(bif));

    genvar gi, ti;
    generate
        for (gi = 0; gi < NUM_COLS; gi++) begin : g_bank
            for (ti = 0; ti < SRAM_VERT_FOLD_FACTOR; ti++) begin : g_subarray
                logic rdone [SRAM_VERT_FOLD_FACTOR];
                logic wdone [SRAM_VERT_FOLD_FACTOR]; 
                logic [ELEM_BITS-1:0] rdata [SRAM_VERT_FOLD_FACTOR];

                logic is_data_in_arr = (bif.cntrl_spad_req[IDX].slot_mask[gi][SRAM_SUBARRAY_WIDTH_BITS-1:0] == ti); 

                sram_bank #(
                    .READ_LATENCY (2), .WRITE_LATENCY(2), 
                    .HEIGHT(SRAM_SUBARRAY_HEIGHT), .WIDTH(ELEM_BITS)
                ) u_bank (
                    .clk(bif.clk), .n_rst(bif.n_rst), .busy(bif.spad_busy[IDX][gi]), 

                    .ren(bif.cntrl_spad_req[IDX].valid_mask[gi] && bif.cntrl_spad_req[IDX].valid && !bif.cntrl_spad_req.write && is_data_in_arr),
                    .raddr(bif.cntrl_spad_req[IDX].slot_mask[gi][SRAM_SUBARRAY_HEIGHT_BITS-1:0]),
                    .rdone(rdone),
                    .rdata(rdata),

                    .wen(bif.cntrl_spad_req[IDX].xbar.valid_mask[gi] && bif.cntrl_spad_req[IDX].valid && !bif.cntrl_spad_req.write && is_data_in_arr),
                    .waddr(bif.cntrl_spad_req[IDX].xbar.slot_mask[gi][SRAM_SUBARRAY_HEIGHT_BITS-1:0]),
                    .wdone(wdone),
                    .wdata(bif.cntrl_spad_req[IDX].wdata[gi])
                );

                assign bif.spad_cntrl_res[IDX][gi] = (rdone[ti] && is_data_in_arr) || (wdone[ti] && is_data_in_arr); 
                assign bif.spad_xbar_req.rdata[IDX][gi] = rdata[ti]; 
            end 
        end
    endgenerate

    rxbar #(.IDX(IDX)) rxbar (.wif(bif));

    tail #(.IDX(IDX)) tail (.tif(bif));

endmodule