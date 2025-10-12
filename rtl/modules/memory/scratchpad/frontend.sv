`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module frontend #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.frontend_vec fvif, 
    scpad_if.frontend_body fsif
); 
    import scpad_types_pkg::*;
    logic vec_rd_req_valid_syn;
    logic vec_wr_req_valid_syn;
    logic fe_rd_res_valid_syn;
    logic fe_wr_res_valid_syn;

    scpad_if.frontend_vc vcif;

    //pipeline enable
    logic pipe_EN; 
    assign pipe_EN = !fsif.fe_stall[IDX];
    
    // stall vec request bit
    assign fvif.fe_vec_stall[IDX] = fsif.fe_stall[IDX];

    //fe_vc module

    frontend_vc #(.IDX(IDX)) u_frontend_vc (
        .vcif(vcif) // will see about this
    ); 

    ///////////pipeline////////////

    //latch incoming requests from vector core and send to units
    latch #(.T(rd_req_t)) l1a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN && fvif.vec_rd_req_valid[IDX]), .in(fvif.vec_rd_req[IDX]), .out(vcif.vc_read_req[IDX])
    ); 

    latch #(.T(wr_req_t)) l1b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN && fvif.vec_wr_req_valid[IDX]), .in(fvif.vec_wr_req[IDX]), .out(vcif.vc_write_req[IDX])
    ); 

    //latch valid bits from vc

    latch #(.T(logic)) l1c (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(fvif.vec_rd_req_valid[IDX]), .out(vec_rd_req_valid_syn)
    ); 

    latch #(.T(logic)) l1d (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(fvif.vec_wr_req_valid[IDX]), .out(vec_wr_req_valid_syn)
    ); 

    //latch units' output requests to sram controller/xbar

    latch #(.T(rd_req_t)) l2a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(vcif.sram_read_req[IDX]), .out(fsif.fe_rd_req[IDX])
    ); 

    latch #(.T(wr_req_t)) l2b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(vcif.sram_write_req[IDX]), .out(fsif.fe_wr_req[IDX])
    ); 

    //latch valid bits to send to sram/xbar

    latch #(.T(logic)) l2c (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(vec_rd_req_valid_syn), .out(fsif.fe_rd_req_valid[IDX])
    ); 

    latch #(.T(logic)) l2d (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(vec_wr_req_valid_syn), .out(fsif.fe_wr_req_valid[IDX])
    ); 


    ///////////// to sram/xbar /////////////
    ///////////// back from sram/xbar ////////////////

    //latch incoming responses

    latch #(.T(rd_res_t)) l3a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN && fsif.fe_rd_res_valid[IDX]), .in(fsif.fe_rd_res[IDX]), .out(vcif.sram_read_res[IDX])
    ); 

    latch #(.T(wr_res_t)) l3b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN && fsif.fe_wr_res_valid[IDX]), .in(fsif.fe_wr_res[IDX]), .out(vcif.sram_write_res[IDX])
    ); 

    // latch valid bits from sram/xbar

    latch #(.T(logic)) l3c (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(fsif.fe_rd_res_valid[IDX]), .out(fe_rd_res_valid_syn)
    ); 

    latch #(.T(logic)) l3d (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(fsif.fe_wr_res_valid[IDX]), .out(fe_wr_res_valid_syn)
    ); 

    // latch edited responses 

    latch #(.T(rd_res_t)) l4a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(vcif.sram_read_res[IDX]), .out(fvif.vec_rd_res[IDX])
    ); 

    latch #(.T(wr_res_t)) l4b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(vcif.sram_write_res[IDX]), .out(fvif.vec_wr_res[IDX])
    ); 

    // latch valid bits to send to vc

    latch #(.T(logic)) l4c (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(fe_rd_res_valid_syn), .out(fvif.vec_rd_res_valid[IDX]) 
    ); 

    latch #(.T(logic)) l4d (.clk(clk), .n_rst(n_rst), 
        .en(pipe_EN), .in(fe_wr_res_valid_syn), .out(fvif.vec_wr_res_valid[IDX])
    ); 


endmodule