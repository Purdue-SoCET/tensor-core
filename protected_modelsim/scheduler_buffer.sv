`include "scheduler_buffer.vh"


module scheduler_buffer #(
    parameter WORD_W = 32
) (
    input logic CLK,
    output logic nRST,
    scheduler_buffer_if.scheduler mysche 
);

    logic [6:0] wptr, rptr;
    logic clear, flush;
    logic [1:0][WORD_W : 0] fifo, n_fifo [64:0];

    assign ramaddr_rq = fifo[rptr][0][31:0];
    assign ramaddr_ft = fifo[rptr - 1][0][31:0];
    assign ramstore_rq = fifo[rptr][1][31:0];
    assign ramstore_ft = fifo[rptr - 1][1][31:0];
    assign full = (wptr == 7'd64) ? 1'b1; 1'b0;
    

    
    socetlib_counter write_count (.CLK(CLK), .nRST(nRST), .clear(clear|| flush), .count_enable((dWEN || dREN) && ~full), .rollover_value(7'd64), .count_out(wptr));
    socetlib_counter read_count (.CLK(CLK), .nRST(nRST), .clear(clear|| flush), .count_enable(request_done && ~full), .rollover_value(7'd64), .count_out(rptr));


    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            fifo <= '0;
        end else begin
            for (int i = 0; i < 65; i++) begin
                fifo[i] <= n_fifo[i];
            end
        end
    end


    always_comb begin
        clear = 1'b0;
        flush = 1'b0
        for (int i = 0; i < 65; i++) begin
            n_fifo[i] = fifo[i];
        end

        if (dREN) begin
            n_fifo[wptr][0] = {1'b1; ramaddr};
        end else if (dWEN) begin
            n_fifo[wptr][0] = {1'b0;ramaddr};
            n_fifo[wptr][1] = memstore;
        end

        if (request_done) begin
            n_fifo[rptr] = '0;
            memaddr_callback = fifo[rptr][0]; 
        end

        if (clear) begin
            for (int i = 0; i < 65; i++) begin
                n_fifo[i] = '0;
            end
        end
    end

endmodule