`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module scratchpad (
    input logic clk, n_rst,
    scpad_if.top sif
); 
    import scpad_types_pkg::*;

    backend      u_backend      (.clk(clk), .n_rst(n_rst), .bif (sif));
    frontend     u_frontend     (.clk(clk), .n_rst(n_rst), .fcif(sif));
    frontend_sa  u_frontend_sa  (.clk(clk), .n_rst(n_rst), .fif (sif));
    frontend_vc  u_frontend_vc  (.clk(clk), .n_rst(n_rst), .fif (sif));
    xbar         u_xbar         (.clk(clk), .n_rst(n_rst), .xif (sif));

    ///////////////////////////////////////////////////////////////////////////////

    logic [NUM_COLS-1:0] ren, wen, rdone, wdone;
    logic [ROW_IDX_WIDTH-1:0] raddr, waddr;
    
    genvar gi;
    generate
        for (gi = 0; gi < NUM_COLS; gi++) begin
        sram_bank u_bank_gi #(.READ_LATENCY(2), .WRITE_LATENCY(4)) (
            .clk (clk),
            .ren (ren[gi]),
            .raddr (raddr),
            .rdata (sram_banks_read_vector[gi]),
            .rdone (rdone[gi]), 
            .wen  (wen[gi]),
            .waddr (waddr),
            .wdata (sram_banks_write_vector[gi])
            .wdone (wdone[gi])
        );
        end
    endgenerate

    sram_cntrl u_sram_cntrl (
        .clk(clk), .n_rst(n_rst), .srif(sif), 
        .ren(ren), .wen(wen), 
        .raddr(raddr), .waddr(waddr), 
        .rdone(rdone), .wdone(wdone)
    );

    assign sif.frontend_sram_banks_res.rdata = sram_banks_read_vector;
    assign sram_banks_write_vector = sif.backend_sram_banks_req.wdata; 

    ///////////////////////////////////////////////////////////////////////////////


    
endmodule