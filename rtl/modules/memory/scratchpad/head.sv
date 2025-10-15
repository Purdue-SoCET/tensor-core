import scpad_pkg::*;

module head #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_head hif);

    logic downstream_stall;
    logic be_v, fe_v;
    logic pipe_busy; 
    logic grant_be, grant_fe;

    req_t req_d, req_q;

    always_ff @(posedge hif.clk, negedge hif.n_rst) begin
        if (!hif.n_rst) begin
            pipe_busy <= 1'b0;
        end else begin
            pipe_busy <= (grant_be || grant_fe);
        end
    end

    always_comb begin
        req_d = '0;

        be_v = hif.be_req_valid[IDX];
        fe_v = hif.fe_req_valid[IDX];

        grant_be = (!hif.w_stall) && be_v;
        grant_fe = (!hif.w_stall) && (!be_v) && fe_v;

        if (grant_be) req_d = hif.be_req[IDX];
        else if (grant_fe) req_d = hif.fe_req[IDX];
    end
 
    latch #(.T(req_t)) u_latch_wr (.clk(hif.clk), .n_rst(hif.n_rst), .en(grant_be || grant_fe), .in(req_d), .out(req_q));

    assign downstream_stall = hif.w_stall || hif.r_stall;

    assign hif.stomach_head_req.valid = pipe_busy;
    assign hif.stomach_head_req = req_q;

    assign hif.fe_stall[IDX] = downstream_stall || (fe_v && (pipe_busy || be_v));
    assign hif.be_stall[IDX] = downstream_stall || (be_v && pipe_busy);

endmodule
