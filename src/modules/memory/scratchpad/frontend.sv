`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module frontend (
    input logic clk, n_rst,
    scpad_if.frontend fcif
); 
    import scpad_types_pkg::*;

    // Here we pipeline the following stages: 

    // - Requests from VC and SA come in. 
    // - We let them enter the individual VC and SA Units. 
    //     - We maintain this seperation so that each unit can handle interactions as they wish. 
    //     - We can enable parallel request generation and then stall until the downstream pipe is ready to accept more requests. 
    // - The SRAM requests coming out then get ARB'd, and sent out as a single Frontend SRAM request per cycle. 
    // - The SRAM responses coming back (through the Crossbar btw!) then get routed into the individual units, which latch and hold onto the data until the requesting unit is able to ACK that it's been received. 
    
    // Q: Can we do all of this within a single `frontend` unit? 
    // A: Yes, but having seperate units just gives us the abstraction needed to enable a higher bandwidth -- by being able to decouple the request pipe with the response pipe to both units. 

    //////////////////////////////// Perf/Timing ////////////////////////////////

    // Here, we're checking for backpressure situations. This should only stop the internal pipe sending requests out, or accepting new requests. 
    // Use frontend_ready and pipe_ahead to check starvation/backpressure situations. 
    logic pipe_ahead; 
    assign pipe_ahead = !(&{
        fcif.sram_busy, 
        (fcif.frontend_vc_res.valid & !fcif.vc_read_complete), 
        (fcif.frontend_tca_res.valid & !fcif.tca_read_complete)
    }); 
    assign fcif.frontend_ready = !pipe_ahead; 

    //////////////////////////////// Sub-Modules ////////////////////////////////

    frontend_sa u_frontend_sa ( 
        .clk(clk), .n_rst(n_rst), 
        .fif(tca_req)
    ); 

    frontend_vc u_frontend_sa ( 
        .clk(clk), .n_rst(n_rst), 
        .fif(vc_req)
    ); 

    //////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////// Frontend Request Pipe ///////////////////////////////////
    //////////////////////////////////////////////////////////////////////////////////////

    //////////////////////////////// Requests Enter Frontend ////////////////////////////////

    frontend_req_t tca_req, vc_req; 
    logic arb_decision, sel_idx; 

    // Latch incoming req
    latch #(.T(frontend_req_t)) l1a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.tca_frontend_req), .out(tca_req)
    ); 
    latch #(.T(frontend_req_t)) l1b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.vc_frontend_req), .out(vc_req)
    ); 

    ////////////////////////////// Break into R/W Queues /////////////////////////////////

    sram_r_req_t vc_read_req, tca_read_req, selected_read_req, read_req_to_sram;
    sram_w_req_t vc_write_req, tca_write_req, selected_write_req, write_req_to_sram;  

    // Latch edited requests
    latch #(.T(sram_r_req_t)) l2aa (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.vc_sram_r_banks_req), .out(vc_read_req)
    ); 
    latch #(.T(sram_w_req_t)) l2ab (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.vc_sram_w_banks_req), .out(vc_write_req)
    ); 

    latch #(.T(sram_r_req_t)) l2ba (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.sa_sram_r_banks_req), .out(tca_read_req)
    ); 
    latch #(.T(sram_w_req_t)) l2bb (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.sa_sram_w_banks_req), .out(tca_write_req)
    ); 

    // Decide which R and which W wins. 
    mux #(.IN(2), .OUT(1), .TYPE_T(sram_r_req_t)) u_mux_sram_r_req (
        .in  ( `{ vc_read_req, tca_read_req } ),        
        .sel_idx (!vc_read_req.valid),      
        .out  (selected_read_req)       
    );

    mux #(.IN(2), .OUT(1), .TYPE_T(sram_w_req_t)) u_mux_sram_w_req (
        .in  ( `{ vc_write_req, tca_write_req } ),        
        .sel_idx (!vc_write_req.valid),      
        .out  (selected_write_req)       
    );

    // Latch the winning requests; Send previously latched winners to SRAM.
    latch #(.T(sram_r_req_t)) l3a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(selected_read_req), .out(fcif.frontend_sram_read_req)
    ); 
    latch #(.T(sram_w_req_t)) l3b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(selected_write_req), .out(fcif.frontend_sram_write_req)
    ); 

    //////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////// Frontend Response Pipe /////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////////

    ////////////////////////////// Route to Units /////////////////////////////////

    sram_r_res_t read_res_from_sram, vc_read_res, tca_read_res; 
    sram_w_res_t write_res_from_sram, vc_write_res, tca_write_res; 

    // Latch completed request; Send previously latched request to units. 
    latch #(.T(sram_r_res_t)) l4a (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.frontend_sram_read_res), .out(read_res_from_sram)
    ); 
    latch #(.T(sram_w_res_t)) l4b (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(fcif.frontend_sram_write_res), .out(write_res_from_sram)
    ); 

    // Take latched responses, decide where to route. 
    demux #(.IN(1), .OUT(2), .TYPE_T(sram_r_res_t)) u_demux_frontend_r_res (
        .in  ( read_res_from_sram ),        
        .sel_idx (!read_res_from_sram.int_id[0]),      
        .out  ( `{ vc_read_res, tca_read_res } )       
    );
    demux #(.IN(1), .OUT(2), .TYPE_T(sram_w_res_t)) u_demux_frontend_w_res (
        .in  ( write_res_from_sram ),        
        .sel_idx (!write_res_from_sram.int_id[0]),      
        .out  ( `{ vc_write_res, tca_write_res } )       
    );

    // Map the busses properly into each unit. 
    latch #(.T(sram_r_res_t)) l5aa (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(vc_read_res), .out(fcif.vc_sram_r_banks_res)
    ); 
    latch #(.T(sram_w_res_t)) l5ab (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(vc_write_res), .out(fcif.vc_sram_w_banks_res)
    ); 

    latch #(.T(sram_r_res_t)) l5ba (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(tca_read_res), .out(fcif.sa_sram_r_banks_res)
    ); 
    latch #(.T(sram_w_res_t)) l5bb (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(tca_write_res), .out(fcif.sa_sram_w_banks_res)
    ); 

    ////////////////////////////// Requests leave Frontend ///////////////////////////////

    // u_frontend_sa.frontend_sa_res and u_frontend_vc.frontend_vc_res; 

endmodule