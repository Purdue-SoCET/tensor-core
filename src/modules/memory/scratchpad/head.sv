`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module head #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.spad_head hif
);
    import scpad_types_pkg::*;

    logic downstream_stall;
    logic be_rd_v, fe_rd_v;
    logic be_wr_v, fe_wr_v;

    logic rd_pipe_busy;
    logic wr_pipe_busy; 

    logic rd_grant_be, rd_grant_fe;
    logic wr_grant_be, wr_grant_fe;

    rd_req_t rd_req_d, rd_req_q;
    wr_req_t wr_req_d, wr_req_q;

    latch #(.T(rd_req_t)) u_latch_rd (.clk(clk), .n_rst(n_rst), .en(rd_grant_be || rd_grant_fe), .in(rd_req_d), .out(rd_req_q));
    latch #(.T(wr_req_t)) u_latch_wr (.clk(clk), .n_rst(n_rst), .en(wr_grant_be || wr_grant_fe), .in(wr_req_d), .out(wr_req_q));

    always_ff @(posedge clk, negedge n_rst) begin
        if (!n_rst) begin
            rd_pipe_busy <= 1'b0;
            wr_pipe_busy <= 1'b0;
        end else begin
            rd_pipe_busy <= (rd_grant_be || rd_grant_fe);
            wr_pipe_busy <= (wr_grant_be || wr_grant_fe);
        end
    end

    always_comb begin 
        rd_req_d = '0;

        be_rd_v = hif.be_rd_req_valid[IDX];
        fe_rd_v = hif.fe_rd_req_valid[IDX];

        rd_grant_be = (!hif.r_stall) && be_rd_v;
        rd_grant_fe = (!hif.r_stall) && (!be_rd_v) && fe_rd_v;

        if (rd_grant_be) rd_req_d = hif.be_rd_req[IDX];
        else if (rd_grant_fe) rd_req_d = hif.fe_rd_req[IDX];
    end 

    always_comb begin
        wr_req_d = '0;

        be_wr_v = hif.be_wr_req_valid[IDX];
        fe_wr_v = hif.fe_wr_req_valid[IDX];

        wr_grant_be = (!hif.w_stall) && be_wr_v;
        wr_grant_fe = (!hif.w_stall) && (!be_wr_v) && fe_wr_v;

        if (wr_grant_be) wr_req_d = hif.be_wr_req[IDX];
        else if (wr_grant_fe) wr_req_d = hif.fe_wr_req[IDX];
    end
 
    assign downstream_stall = hif.w_stall || hif.r_stall;

    assign hif.stomach_head_rd_req_valid = rd_pipe_busy; 
    assign hif.stomach_head_rd_req = rd_req_q;
    assign hif.stomach_head_wr_req_valid = wr_pipe_busy;
    assign hif.stomach_head_wr_req = wr_req_q;

    assign hif.fe_stall[IDX] = downstream_stall || (fe_rd_v && (rd_pipe_busy || be_rd_v)) || (fe_wr_v && (wr_pipe_busy || be_wr_v));
    assign hif.be_stall[IDX] = downstream_stall || (be_rd_v && rd_pipe_busy) || (be_wr_v && wr_pipe_busy);


endmodule
