`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module w_fsm(
    input logic clk, n_rst,
    scpad_if.frontend sif
);
    import scpad_types_pkg::*;

    typedef enum logic [2:0] {W_IDLE, W_MAKE_XBAR_DESC, W_REQ_XBAR, W_ISSUE_SRAM, W_RESP_DONE} state_t;
    state_t state, nextstate;

    always_comb begin : next_state_logic
        casez (state_t)
            W_IDLE: begin
                
            end
            W_MAKE_XBAR_DESC: begin
                
            end
            W_REQ_XBAR: begin
                
            end
            W_ISSUE_SRAM: begin
                
            end
            W_RESP_DONE: begin
                
            end
            default: nextstate = W_IDLE;
        endcase
    end

    always_ff @( posedge clk, negedge n_rst ) begin : state_transition
        if(!n_rst) begin
            nextstate <= W_IDLE;
        end else begin
            nextstate <= nextstate;
        end
    end

    always_comb begin : output_comb_logic
        casez (state_t)
            W_IDLE: begin
                
            end
            W_MAKE_XBAR_DESC: begin
                
            end
            W_REQ_XBAR: begin
                
            end
            W_ISSUE_SRAM: begin
                
            end
            W_RESP_DONE: begin
                
            end
        endcase
    end

endmodule