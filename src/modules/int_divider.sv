module int_divider #(
    parameter SIZE = 23,
    parameter SKIP = 11
)(
    input logic CLK, nRST, en,
    input logic [SIZE-1:0] x, y,
    output logic [SIZE-1:0] result,
    output logic done
);

typedef enum logic {IDLE, DIV} state_t;
state_t state, next_state;

logic [SIZE:0] q, next_q, a, next_a, m, next_m;
logic [3:0] n, next_n;
always_ff @(posedge CLK) begin
    if (~nRST) begin
        state <= IDLE;
        q <= 0;
        m <= 0;
        a <= 0;
        n <= 0;
    end else begin
        state <= next_state;
        q <= next_q;
        m <= next_m;
        a <= next_a;
        n <= next_n;
    end
end

logic [SIZE:0] init_q, init_a;
always_comb begin
    next_state = state;
    next_q = q;
    next_m = m;
    next_a = a;
    next_n = n;
    case (state)
        IDLE: begin
            if (en) begin
                next_state = DIV;
                init_q = {1'b0, x} << SKIP;
                next_m = {1'b0, y};
                init_a = x[SIZE-1 -: SKIP-1];
                next_n = SIZE - SKIP - 1;
                // Do first iteration immediately
                next_a = init_a[SIZE] ? {init_a[SIZE-1:0], init_q[SIZE]} + next_m
                                      : {init_a[SIZE-1:0], init_q[SIZE]} - next_m;
                next_q = {init_q[SIZE-1:0], ~next_a[SIZE]};
            end
        end
        DIV: begin
            next_a = a[SIZE] ? {a[SIZE-1:0], q[SIZE]} + m : {a[SIZE-1:0], q[SIZE]} - m;
            next_q = {q[SIZE-1:0], ~next_a[SIZE]};
            next_n = n - 1;
            if (n == 0) next_state = IDLE;
        end
    endcase
end

assign result = next_q[SIZE-1:0];
assign done = (state == DIV && n == 0);

endmodule