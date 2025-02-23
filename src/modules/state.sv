`include "types_pkg.vh"

module state_machine(input CLK, negedge nRST);

typedef enum [2:0] states {IDLE, next1, next2, next3, next4, endS};

states state, next_state;

always_ff @(posedge CLK, negedge nRST) begin
    if(nRST == 0) begin
        state <= IDLE;
    end
    else begin
        state <= next_state;
    end
end

always_comb begin
    next_state = state;
    if(input == 1) begin
        next_state = next1;
    end
    else begin
    end
end

endmodule