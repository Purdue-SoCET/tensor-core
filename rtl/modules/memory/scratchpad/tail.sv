import scpad_pkg::*;

module tail  #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_tail tif);

    sel_rd_res_t rd_res_q;
    sel_wr_res_t wr_res_q;

    latch #(.T(sel_rd_res_t)) u_latch_rd (.clk(tif.clk), .n_rst(tif.n_rst), .en(tif.stomach_tail_rd_res[IDX].valid), .in(tif.stomach_tail_rd_res[IDX]), .out(rd_res_q));

    latch #(.T(sel_wr_res_t)) u_latch_wr (.clk(tif.clk), .n_rst(tif.n_rst), .en(tif.stomach_tail_wr_res[IDX].valid), .in(tif.stomach_tail_wr_res[IDX]), .out(wr_res_q));

    always_comb begin
        tif.fe_rd_res_valid[IDX] = 1'b0; tif.fe_wr_res_valid[IDX] = 1'b0;
        tif.be_rd_res_valid[IDX] = 1'b0; tif.be_wr_res_valid[IDX] = 1'b0;

        tif.fe_rd_res[IDX] = '0; tif.fe_wr_res[IDX] = '0;
        tif.be_rd_res[IDX] = '0; tif.be_wr_res[IDX] = '0;

        if (rd_res_q.valid) begin
            case (rd_res_q.src)
                SRC_FE: begin
                    tif.fe_rd_res_valid[IDX] = 1'b1;
                    tif.fe_rd_res.rdata[IDX] = rd_res_q.rdata[IDX];
                end
                SRC_BE: begin
                    tif.be_rd_res_valid = 1'b1;
                    tif.be_rd_res.rdata[IDX] = rd_res_q.rdata[IDX];
                end
            endcase
        end

        if (wr_res_q.valid) begin
            case (wr_res_q.src)
                SRC_FE: tif.fe_wr_res_valid[IDX] = 1'b1;
                SRC_BE: tif.be_wr_res_valid[IDX] = 1'b1;
            endcase
        end
    end

endmodule
