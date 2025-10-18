import scpad_pkg::*;

module scpad_cntrl #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.sram_ctrl srif);

    logic wr_fifo_empty; 
    logic rd_fifo_empty; 

    // Little's Law: L = lambda * W. L is buffer depth, lambda is arrival rate, and W is length of value in buffer. Lambda = 1; W = MAX_SRAM_DELAY
    // Basic queue-theory. Allocate enough to ensure drain matches fill. 
    // Make stall uncommon. 
    sync_fifo #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_req_t))) wr_fifo (
        .clk(srif.clk),
        .rstn(srif.n_rst),
        .wr_en(srif.xbar_cntrl_req[IDX].valid),
        .din(srif.xbar_cntrl_req[IDX].write ? srif.xbar_cntrl_req[IDX] : '0),
        .rd_en(!{&spad_busy}),
        .dout(srif.cntrl_spad_req[IDX]),
        .full(srif.w_stall),
        .empty(wr_fifo_empty)
    );

    sync_fifo #(.DEPTH(MAX_SRAM_DELAY), .DWIDTH($bits(sel_req_t))) rd_fifo (
        .clk(srif.clk),
        .rstn(srif.n_rst),
        .wr_en(srif.head_stomach_req[IDX].valid),
        .din(!srif.xbar_cntrl_req[IDX].write ? srif.head_stomach_req[IDX] : '0),
        .rd_en(!{&spad_busy}),
        .dout(srif.cntrl_spad_req[IDX]),
        .full(srif.r_stall),
        .empty(rd_fifo_empty)
    );

    `ifndef SYNTHESIS
        always_ff @(posedge srif.clk, negedge srif.n_rst) begin
            if (!srif.n_rst) begin
                srif.scpad_backpressure_buffer_read_empty[IDX]  <= '0;
                srif.scpad_backpressure_buffer_write_empty[IDX] <= '0;
                srif.scpad_backpressure_buffer_read_stall[IDX]  <= '0;
                srif.scpad_backpressure_buffer_write_stall[IDX] <= '0;
            end else begin
                if (rd_fifo_empty) srif.scpad_backpressure_buffer_read_empty[IDX] <= srif.scpad_backpressure_buffer_read_empty[IDX] + 1;
                if (wr_fifo_empty) srif.scpad_backpressure_buffer_write_empty[IDX] <= srif.scpad_backpressure_buffer_write_empty[IDX] + 1;
                if (srif.r_stall) srif.scpad_backpressure_buffer_read_stall[IDX] <= srif.scpad_backpressure_buffer_read_stall[IDX] + 1;
                if (srif.w_stall) srif.scpad_backpressure_buffer_write_stall[IDX] <= srif.scpad_backpressure_buffer_write_stall[IDX] + 1;
            end
        end
    `endif

endmodule