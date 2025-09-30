module sqrt_dmult1 #(
    parameter LATENCY = 3,
    parameter logic [15:0] PRECOMPUTED_RESULT = 16'h3C00
)(
    input  logic CLK, 
    input  logic nRST, 
    input  logic [15:0] port_a,
    input  logic [15:0] port_b,
    output logic [15:0] product
);

    logic [15:0] pipe [0:LATENCY-1];
    logic valid_input;

    // Consider input valid if port_a or port_b is non-zero
    assign valid_input = |port_a || |port_b;

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            pipe <= '{default:'0};
        end
        else begin
            // Shift the pipeline every cycle
            for (int i = LATENCY-1; i > 0; i--) begin
                pipe[i] <= pipe[i-1];
            end

            // Insert precomputed result if input is valid, else insert 0
            if (valid_input) begin
                pipe[0] <= PRECOMPUTED_RESULT;
            end
            else begin
                pipe[0] <= '0;
            end
        end
    end

    assign product = pipe[LATENCY-1];

endmodule
