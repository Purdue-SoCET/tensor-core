import scpad_pkg::*;

module frontend #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.frontend_vec fvif, scpad_if.frontend_body fsif); 

    // grab clk and n_rst from any 

    // pipeline enable
    logic pipe_EN;
    assign pipe_EN = !fsif.fe_stall[IDX];

    // propagate frontend stall back to the vector core
    assign fvif.fe_vec_stall[IDX] = fsif.fe_stall[IDX];

    // internal VC interface
    scpad_if.frontend_vc vcif();

    // instantiate internal frontend_vc
    frontend_vc #(.IDX(IDX)) u_frontend_vc (.vcif(vcif));

    // latch incoming request from Vector Core into the FE->Body path
    // only latch when the incoming request is valid and pipeline enabled
    latch #(.T(req_t)) u_latch_req (
        .clk (clk),
        .n_rst(n_rst),
        .en  (pipe_EN && fvif.vec_req[IDX].valid),
        .in  (fvif.vec_req[IDX]),
        .out (fsif.fe_req[IDX])
    );

    // latch response from Body back to Vector Core
    latch #(.T(res_t)) u_latch_res (
        .clk (clk),
        .n_rst(n_rst),
        .en  (pipe_EN && fsif.fe_res[IDX].valid),
        .in  (fsif.fe_res[IDX]),
        .out (fvif.vec_res[IDX])
    );

endmodule