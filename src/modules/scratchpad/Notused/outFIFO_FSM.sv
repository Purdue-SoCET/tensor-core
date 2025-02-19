`include "types_pkg.vh"
`include "outFIFO_FSM_if.vh"

module outFIFO_FSM (
    input logic CLK, nRST,
    outFIFO_FSM_if.sp spif
);

    typedef enum logic [1:0] {
        IDLE, DECODE
    } state_t;

    state_t state, n_state;

    always_ff @(posedge CLK, negedge nRST) begin
        if (nRST == 1'b0) begin
            state <= IDLE;
        end
        else begin
            state <= n_state;
        end
    end

    always_comb begin
        n_state = state;
        case (state)
        IDLE: begin
            if (~spif.instr_FIFO_empty) begin
                n_state = DECODE;
            end
        end
        DECODE: begin
            if (spif.instr_FIFO_empty) begin
                n_state = IDLE;
            end
        end
        endcase
    end

    always_comb begin
        spif.instr_FIFO_empty = 1'b0;
        case (state)
        IDLE: begin

        end
        DECODE: begin
            
        end
        endcase
    end

endmodule