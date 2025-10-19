import scpad_pkg::*;

module tail #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_tail tif);

    sel_res_t res_q;

    latch #(.T(sel_res_t)) u_latch_wr (.clk(tif.clk), .n_rst(tif.n_rst), .en(tif.stomach_tail_res[IDX].valid), .in(tif.stomach_tail_res[IDX]), .out(res_q));

    always_comb begin
        tif.fe_res[IDX] = '0;
        tif.be_res[IDX] = '0;

        if (res_q.valid && !res_q.write) begin
            case (res_q.src)
                SRC_FE: begin
                    tif.fe_res[IDX].valid = 1'b1;
                    tif.fe_res.rdata[IDX] = res_q.rdata[IDX];
                end
                SRC_BE: begin
                    tif.be_res[IDX].valid = 1'b1;
                    tif.be_res.rdata[IDX] = res_q.rdata[IDX];
                end
            endcase
        end
        else if (res_q.valid && res_q.write) begin
            case (res_q.src)
                SRC_FE: tif.fe_res[IDX].valid = 1'b1;
                SRC_BE: tif.be_res[IDX].valid = 1'b1;
            endcase
        end
    end

endmodule
