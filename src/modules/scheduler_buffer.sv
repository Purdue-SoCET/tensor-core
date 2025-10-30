`include "scheduler_buffer_if.vh"
`include "socetlib_counter_if.vh"


module scheduler_buffer #(
    parameter WORD_W = 32
) (
    input logic CLK,
    input logic nRST,
    scheduler_buffer_if.scheduler mysche 
);

    logic [6:0] wptr, rptr;
    logic clear, flush;
    logic full;
    integer i;
    // logic [1:0][WORD_W : 0] [64:0]fifo;
    // logic [1:0][WORD_W : 0] [64:0]n_fifo;

    logic [64:0][1:0][WORD_W + 1:0] fifo, n_fifo;

    assign mysche.ramaddr_rq = fifo[rptr][0][31:0];
    assign mysche.ramaddr_rq_ft = fifo[rptr - 1][0][31:0];
    assign mysche.ramstore_rq = fifo[rptr][1][31:0];
    assign mysche.ramstore_rq_ft = fifo[rptr - 1][1][31:0];
    
    assign mysche.ramREN_curr = fifo[rptr][0][33:32] == 2'b01 ? 1'b1 : 1'b0;
    assign mysche.ramREN_ftrt = fifo[rptr - 1][0][32] == 2'b01 ? 1'b1 : 1'b0;

    assign mysche.ramWEN_curr = fifo[rptr][0][33:32] == 2'b10 ? 1'b1 : 1'b0;
    assign mysche.ramWEN_ftrt = fifo[rptr - 1][0][32] == 2'b10 ? 1'b1 : 1'b0;


    assign full = (wptr == (rptr - 1)) ? 1'b1: 1'b0;
    

    
    
    socetlib_counter #(.NBITS(7)) write_count (.CLK(CLK), .nRST(nRST), .clear(clear|| flush), .count_enable((mysche.dWEN || mysche.dREN) && ~full), .overflow_val(7'd64), .count_out(wptr));
    socetlib_counter #(.NBITS(7)) read_count (.CLK(CLK), .nRST(nRST), .clear(clear|| flush), .count_enable(mysche.request_done && ~full), .overflow_val(7'd64), .count_out(rptr));


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
        flush = 1'b0;
        for (i = 0; i < 65; i++) begin
            n_fifo[i] = fifo[i];
        end

        if (mysche.dREN) begin
            n_fifo[wptr][0] = {2'b01, mysche.ramaddr};
        end else if (mysche.dWEN) begin
            n_fifo[wptr][0] = {2'b10,mysche.ramaddr};
            n_fifo[wptr][1] = mysche.memstore;
        end

        if (mysche.request_done) begin
            n_fifo[rptr] = '0;
            mysche.memaddr_callback = fifo[rptr][0]; 
        end

        if (clear) begin
            for (i = 0; i < 65; i++) begin
                n_fifo[i] = '0;
            end
        end
    end

endmodule