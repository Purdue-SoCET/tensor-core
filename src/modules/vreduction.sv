`include "vector_types.vh"
`include "vreduction_if.vh"
`include "vreduction_alu_if.vh"

module vreduction #(
    parameter int LANES = 16
) (
    input logic CLK,
    input logic nRST,
    vreduction_if.ruif vruif
);
    localparam int LEVELS = $clog2(LANES);
    localparam int PIPE_STAGES = LEVELS + 2;
    
    // Import vector types
    import vector_pkg::*;

    // Convert fp16_t array to logic array for reduction tree
    logic [15:0] tree_data_in [LANES-1:0];
    logic [15:0] tree_data_out;
    logic tree_valid_out;

    always_comb begin
        for (int i = 0; i < LANES; i++) begin
            tree_data_in[i] = vruif.lane_input[i];
        end
    end

    // Instantiate the pipelined reduction tree
    reduction_tree #(
        .LANES(LANES)
    ) reduction_tree (
        .CLK(CLK),
        .nRST(nRST),
        .data_in(tree_data_in),
        .alu_op(vruif.reduction_type),
        .valid_in(vruif.input_valid),
        .data_out(tree_data_out),
        .valid_out(tree_valid_out)
    );

    //pipeline allignment for the needed output signals
    logic [4:0] imm_final;
    sqrt_pipe #(
        .DATA_WIDTH(5),
        .STAGES(PIPE_STAGES)
    ) imm_pipe (
        .CLK(CLK),
        .nRST(nRST),
        .enable(vruif.input_valid),
        .data_in(vruif.imm),
        .data_out(imm_final)
    );
    logic broadcast_final;
    sqrt_pipe #(
        .DATA_WIDTH(5),
        .STAGES(PIPE_STAGES)
    ) broadcast_pipe (
        .CLK(CLK),
        .nRST(nRST),
        .enable(vruif.input_valid),
        .data_in(vruif.broadcast),
        .data_out(broadcast_final)
    );
    logic clear_final;
    sqrt_pipe #(
        .DATA_WIDTH(5),
        .STAGES(PIPE_STAGES)
    ) clear_pipe (
        .CLK(CLK),
        .nRST(nRST),
        .enable(vruif.input_valid),
        .data_in(vruif.clear),
        .data_out(clear_final)
    );

    fp16_t vector_pipe [0:PIPE_STAGES-1][NUM_ELEMENTS-1:0];

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            for (int s = 0; s < PIPE_STAGES; s++)
                for (int i = 0; i < NUM_ELEMENTS; i++)
                    vector_pipe[s][i] <= '{default: '0};
        end else begin
            // Stage 0: capture new input only when valid
            for (int i = 0; i < NUM_ELEMENTS; i++)
                vector_pipe[0][i] <= vruif.input_valid ? vruif.vector_input[i] : '{default:'0};

            // Shift data through remaining stages
            for (int s = 1; s < PIPE_STAGES; s++)
                for (int i = 0; i < NUM_ELEMENTS; i++)
                    vector_pipe[s][i] <= vector_pipe[s-1][i];
        end
    end

    // Final value from reduction (convert back to fp16_t)
    fp16_t final_value;
    assign final_value = tree_data_out;

    // Temporary vector for combinational logic
    fp16_t final_vector [NUM_ELEMENTS-1:0];

    always_comb begin
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            if (broadcast_final) begin
                final_vector[i] = final_value;
            end
            else if (clear_final) begin
                final_vector[i] = (i == int'(imm_final)) ? final_value : '0;
            end
            else begin
                final_vector[i] = (i == int'(imm_final)) ? final_value : vector_pipe[PIPE_STAGES-1][i];
            end
        end
    end


    fp16_t registered_output [NUM_ELEMENTS-1:0];
    logic   registered_valid;

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i < NUM_ELEMENTS; i++)
                registered_output[i] <= '{default: '0};
            registered_valid <= 1'b0;
        end else begin
            for (int i = 0; i < NUM_ELEMENTS; i++)
                registered_output[i] <= final_vector[i];
            registered_valid <= tree_valid_out;
        end
    end

    always_comb begin
        for (int i = 0; i < NUM_ELEMENTS; i++)
            vruif.vector_output[i] = registered_output[i];
        vruif.output_valid = registered_valid;
    end

endmodule