`include "vector_types.vh"
`include "vreduction_if.vh"
`include "vreduction_alu_if.vh"

module vreduction #(
    parameter int WIDTH = 16
) (
    input logic CLK,
    input logic nRST,
    vreduction_if.ruif vruif
);
    localparam int LEVELS = $clog2(WIDTH);
    
    // Import vector types
    import vector_pkg::*;

    // Registers for each level
    fp16_t level_regs [LEVELS+1][WIDTH-1:0];
    fp16_t alu_out [LEVELS-1:0][WIDTH/2-1:0];

    // Generate reduction tree
    generate
        for (genvar g_level = 0; g_level < LEVELS; g_level++) begin : gen_levels
            localparam int NODES = WIDTH >> (g_level + 1);

            for (genvar g_node = 0; g_node < NODES; g_node++) begin : gen_nodes
                // Instantiate ALU interface
                vreduction_alu_if alu_if();

                // Connect interface signals
                assign alu_if.value_a = level_regs[g_level][2*g_node];
                assign alu_if.value_b = level_regs[g_level][2*g_node + 1];
                assign alu_if.alu_op = vruif.reduction_type;
                
                // Instantiate ALU
                vreduction_alu alu_inst (
                    .CLK(CLK),
                    .nRST(nRST),
                    .vraluif(alu_if)
                );

                // Capture output
                assign alu_out[g_level][g_node] = alu_if.value_out;
            end
        end
    endgenerate

    //alu and register connections
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            // Reset all registers
            for (int i = 0; i <= LEVELS; i++) begin
                for (int j = 0; j < WIDTH; j++) begin
                    level_regs[i][j] <= '0;
                end
            end
        end 
        else begin
            // Register before first set of ALUs
            for (int i = 0; i < WIDTH; i++) begin
                level_regs[0][i] <= vruif.lane_input[i];
            end
            
            // Connect ALU outputs to next pipeline stage
            for (int i = 0; i < LEVELS; i++) begin
                for (int j = 0; j < (WIDTH >> (i+1)); j++) begin
                    level_regs[i+1][j] <= alu_out[i][j];
                end
            end
        end
    end

    //valid signal pipeline
    logic [LEVELS:0] level_valid;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            level_valid <= '0;
        end 
        else begin
            // Propagate valid through the pipeline
            level_valid[0] <= vruif.input_valid;
            for (int i = 0; i < LEVELS; i++) begin
                level_valid[i+1] <= level_valid[i];
            end
        end
    end

    fp16_t vector_input_pipe [LEVELS:0][NUM_ELEMENTS-1:0];

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i <= LEVELS; i++) begin
                for (int j = 0; j < NUM_ELEMENTS; j++) begin
                    vector_input_pipe[i][j] <= '{default: '0};
                end
            end
        end 
        else begin
            // grab inputs
            for (int j = 0; j < NUM_ELEMENTS; j++) begin
                vector_input_pipe[0][j] <= vruif.vector_input[j];
            end

            // shift through the pipe
            for (int i = 0; i < LEVELS; i++) begin
                for (int j = 0; j < NUM_ELEMENTS; j++) begin
                    vector_input_pipe[i+1][j] <= vector_input_pipe[i][j];
                end
            end
        end
    end



    // IMM pipeline (already in your design)
    logic [LEVELS:0][4:0] imm_pipe;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i <= LEVELS; i++)
                imm_pipe[i] <= 0;
        end
        else begin
            imm_pipe[0] <= vruif.imm;
            for (int i = 0; i < LEVELS; i++)
                imm_pipe[i+1] <= imm_pipe[i];
        end
    end

    // Pipeline control signals
    logic [LEVELS:0] broadcast_pipe, clear_pipe;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i <= LEVELS; i++) begin
                broadcast_pipe[i] <= 0;
                clear_pipe[i] <= 0;
            end
        end
        else begin
            broadcast_pipe[0] <= vruif.broadcast;
            clear_pipe[0] <= vruif.clear;
            for (int i = 0; i < LEVELS; i++) begin
                broadcast_pipe[i+1] <= broadcast_pipe[i];
                clear_pipe[i+1] <= clear_pipe[i];
            end
        end
    end

    // Final value from reduction
    fp16_t final_value;

    // Temporary vector for combinational logic
    fp16_t final_vector [NUM_ELEMENTS-1:0];

    always_comb begin
        final_value = level_regs[LEVELS][0];

        for (int i = 0; i < NUM_ELEMENTS; i++) begin
            if (broadcast_pipe[LEVELS]) begin
                // Broadcast mode: every element = reduction result
                final_vector[i] = final_value;
            end
            else if (clear_pipe[LEVELS]) begin
                // Clear + partial write: only imm index gets value, others zero
                final_vector[i] = (i == int'(imm_pipe[LEVELS])) ? final_value : '0;
            end
            else begin
                // Regular partial write: only imm index gets value, others retain previous output
                final_vector[i] = (i == int'(imm_pipe[LEVELS])) ? final_value : vector_input_pipe[LEVELS][i];
            end
        end
    end

    // Registered outputs
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            vruif.vector_output <= '{default: '0};
            vruif.output_valid <= 0;
        end
        else begin
            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                vruif.vector_output[i] <= final_vector[i];
            end
            // Output valid is already pipelined
            vruif.output_valid <= level_valid[LEVELS];
        end
    end

endmodule