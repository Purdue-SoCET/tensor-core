import scpad_pkg::*;

module head #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.spad_head hif);

    // Stalls
    logic downstream_stall;
    logic pipe_busy; 

    // Tracking grants
    // Need to hold fe_stall high on the N+1th cycle to ensure we don't overwrite the request. 
    logic be_v, fe_v;
    logic grant_be, grant_fe;

    // Intermediate
    req_t req_d;

    always_ff @(posedge hif.clk, negedge hif.n_rst) begin
        if (!hif.n_rst) pipe_busy <= 1'b0;
        else pipe_busy <= (grant_be || grant_fe);
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
 
    // head_stomach_req will either go into the scpad_cntrl FIFO or xbar. 
    // No need to latch here -> LATCH_INT
    assign hif.head_stomach_req = fvif.vec_req[IDX];

    assign downstream_stall = hif.w_stall || hif.r_stall;
    assign hif.fe_stall[IDX] = downstream_stall || (fe_v && (pipe_busy || be_v));
    assign hif.be_stall[IDX] = downstream_stall || (be_v && pipe_busy);

endmodule
