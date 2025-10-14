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
    
    // Import vector types
    import vector_pkg::*;

    // Convert fp16_t array to logic array for reduction tree
    logic [15:0] tree_data_in [LANES-1:0];
    logic [15:0] tree_data_out;
    logic tree_valid_out;

    // Convert input vector to packed logic array
    always_comb begin
        for (int i = 0; i < LANES; i++) begin
            tree_data_in[i] = vruif.lane_input[i];
        end
    end

    // Instantiate the pipelined reduction tree
    pipelined_reduction_tree #(
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

    // Pipeline for vector passthrough (to align with reduction latency)
    // Reduction tree has LEVELS+2 latency: input reg + LEVELS tree stages + output reg
    fp16_t vector_input_pipe [LEVELS+2:0][NUM_ELEMENTS-1:0];

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i <= LEVELS+2; i++) begin
                for (int j = 0; j < NUM_ELEMENTS; j++) begin
                    vector_input_pipe[i][j] <= '{default: '0};
                end
            end
        end 
        else begin
            // Grab inputs
            for (int j = 0; j < NUM_ELEMENTS; j++) begin
                vector_input_pipe[0][j] <= vruif.vector_input[j];
            end

            // Shift through the pipe
            for (int i = 0; i <= LEVELS+1; i++) begin
                for (int j = 0; j < NUM_ELEMENTS; j++) begin
                    vector_input_pipe[i+1][j] <= vector_input_pipe[i][j];
                end
            end
        end
    end

    // IMM pipeline
    logic [LEVELS+2:0][4:0] imm_pipe;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i <= LEVELS+2; i++)
                imm_pipe[i] <= 0;
        end
        else begin
            imm_pipe[0] <= vruif.imm;
            for (int i = 0; i <= LEVELS+1; i++)
                imm_pipe[i+1] <= imm_pipe[i];
        end
    end

    // Pipeline control signals
    logic [LEVELS+2:0] broadcast_pipe, clear_pipe;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i <= LEVELS+2; i++) begin
                broadcast_pipe[i] <= 0;
                clear_pipe[i] <= 0;
            end
        end
        else begin
            broadcast_pipe[0] <= vruif.broadcast;
            clear_pipe[0] <= vruif.clear;
            for (int i = 0; i <= LEVELS+1; i++) begin
                broadcast_pipe[i+1] <= broadcast_pipe[i];
                clear_pipe[i+1] <= clear_pipe[i];
            end
        end
    end

    // Final value from reduction (convert back to fp16_t)
    fp16_t final_value;
    assign final_value = tree_data_out;

    // Temporary vector for combinational logic
    fp16_t final_vector [NUM_ELEMENTS-1:0];

    always_comb begin
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            if (broadcast_pipe[LEVELS+2]) begin
                // Broadcast mode: every element = reduction result
                final_vector[i] = final_value;
            end
            else if (clear_pipe[LEVELS+2]) begin
                // Clear + partial write: only imm index gets value, others zero
                final_vector[i] = (i == int'(imm_pipe[LEVELS+2])) ? final_value : '0;
            end
            else begin
                // Regular partial write: only imm index gets value, others retain previous output
                final_vector[i] = (i == int'(imm_pipe[LEVELS+2])) ? final_value : vector_input_pipe[LEVELS+2][i];
            end
        end
    end

    // Direct output assignment (reduction tree output is already registered)
    always_comb begin
        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            vruif.vector_output[i] = final_vector[i];
        end
        vruif.output_valid = tree_valid_out;
    end

endmodule