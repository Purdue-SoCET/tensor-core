`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module scratchpad (
    input logic clk, n_rst,
    scpad_if.top sif
); 
    import scpad_types_pkg::*;



    logic pipe_ahead; 
    assign pipe_ahead = 1'b1; // What are the backpressure situations? 

    /////////////////////////////// Frontend Control ///////////////////////////////

    frontend u_frontend (.clk(clk), .n_rst(n_rst), .fcif(sif));
    backend u_backend (.clk(clk), .n_rst(n_rst), .bif (sif));


    xbar read_xbar (.clk(clk), .n_rst(n_rst), .xif (sif));
    xbar read_xbar (.clk(clk), .n_rst(n_rst), .xif (sif));

    xbar write_xbar (.clk(clk), .n_rst(n_rst), .xif (sif));
    xbar write_xbar (.clk(clk), .n_rst(n_rst), .xif (sif));

    /////////////////////////////// SRAM Control ///////////////////////////////

    logic [NUM_COLS-1:0] ren [NUM_SCPADS];
    logic [NUM_COLS-1:0] wen [NUM_SCPADS];
    logic [NUM_COLS-1:0] rdone [NUM_SCPADS];
    logic [NUM_COLS-1:0] wdone [NUM_SCPADS];

    logic [ROW_IDX_WIDTH-1:0] raddr [NUM_SCPADS];
    logic [ROW_IDX_WIDTH-1:0] waddr [NUM_SCPADS];

    logic [NUM_COLS-1:0][DATA_W-1:0] sram_banks_read_vector [NUM_SCPADS];
    logic [NUM_COLS-1:0][DATA_W-1:0] sram_banks_write_vector [NUM_SCPADS];

    mux #(.IN(2), .OUT(1), .TYPE_T(sram_r_req_t)) u_mux_sram_r_req (
        .in  ( `{ sif.frontend_sram_read_req, sif.backend_sram_read_req } ),        
        .sel_idx (!sif.frontend_sram_read_req.valid),      
        .out  (sif.sram_read_req)       
    );
    mux #(.IN(2), .OUT(1), .TYPE_T(sram_w_req_t)) u_mux_sram_r_req (
        .in  ( `{ sif.frontend_sram_write_req, sif.backend_sram_write_req } ),        
        .sel_idx (!sif.frontend_sram_write_req.valid),      
        .out  (sif.sram_write_req)       
    );

    sram_cntrl u_sram_cntrl (
        .clk(clk), .n_rst(n_rst), .srif(sif),
        .ren(ren), .wen(wen),
        .raddr(raddr), .waddr(waddr),
        .rdone(rdone), .wdone(wdone),

        .sram_banks_read_vector(sram_banks_read_vector),
        .sram_banks_write_vector(sram_banks_write_vector)
    );

    genvar gi, ti;
    generate
    for (ti = 0; ti < NUM_SCPADS; ti++) begin : g_scpad
        for (gi = 0; gi < NUM_COLS; gi++) begin : g_bank
        sram_bank #(
            .READ_LATENCY (2),
            .WRITE_LATENCY(4)
        ) u_bank (
            .clk(clk),
            .ren(ren[ti][gi]),
            .rdone(rdone[ti][gi]),
            .wen(wen[ti][gi]),
            .wdone(wdone[ti][gi]),
            .raddr(raddr[ti]),
            .waddr(waddr[ti]),
            .rdata(sram_banks_read_vector[ti][gi]),
            .wdata(sram_banks_write_vector[ti][gi])
        );
        end
    end
    endgenerate

    demux #(.IN(1), .OUT(2), .TYPE_T(sram_r_res_t)) u_demux_sram_r_res (
        .in  ( sif.sram_read_res ),        
        .sel_idx (sif.sram_read_res.int_id[1]),      
        .out  ( `{ sif.frontend_sram_read_res, sif.backend_sram_read_res } )       
    );

    demux #(.IN(1), .OUT(2), .TYPE_T(sram_w_res_t)) u_demux_sram_w_res (
        .in  ( sif.sram_write_res ),        
        .sel_idx (sif.sram_write_res.int_id[1]),      
        .out  ( `{ sif.frontend_sram_write_res, sif.backend_sram_write_res } )       
    );


    ///////////////////////////////////////////////////////////////////////////////
    
endmodule