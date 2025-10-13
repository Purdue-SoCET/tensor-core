module sqrt_pipe #(
    parameter int DATA_WIDTH = 16,
    parameter int STAGES = 1
) (
    input logic CLK,
    input logic nRST,
    input logic enable,
    input logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out
);

    logic [DATA_WIDTH-1:0] pipe_regs [0:STAGES-1];

    always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
        pipe_regs <= '{default:'0};
    end
    else begin
        // Stage 0: latch new input only if enable is high
        pipe_regs[0] <= enable ? data_in : pipe_regs[0];

        // Shift remaining stages unconditionally
        for (int i = 1; i < STAGES; i++)
            pipe_regs[i] <= pipe_regs[i-1];
    end
end

    assign data_out = pipe_regs[STAGES-1];
    
endmodule