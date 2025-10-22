`include "vector_types.vh"
`include "vreduction_alu_if.vh"

module reduction_tree #(
    parameter LANES = 16        // Must be power of 2
) (
    input  logic CLK,
    input  logic nRST,
    input  logic [15:0] data_in [LANES-1:0],
    input  logic [1:0]  alu_op,
    input  logic        valid_in,
    output logic [15:0] data_out,
    output logic        valid_out
);

    import vector_pkg::*;

    localparam TREE_DEPTH = $clog2(LANES);
    localparam ALU_LATENCY = 2;

    // Create enough storage for all tree levels, each with ALU_LATENCY stages
    logic [15:0] tree_data [0:TREE_DEPTH][0:ALU_LATENCY][LANES-1:0];
    logic [1:0]  tree_op   [0:TREE_DEPTH][0:ALU_LATENCY];
    logic        tree_valid[0:TREE_DEPTH][0:ALU_LATENCY];

    // Input stage (tree level 0, pipeline stage 0)
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i < LANES; i++)
                tree_data[0][0][i] <= '0;
            tree_op[0][0]   <= 2'b0;
            tree_valid[0][0] <= 1'b0;
        end 
        else begin
            for (int i = 0; i < LANES; i++)
                tree_data[0][0][i] <= data_in[i];
            tree_op[0][0]   <= alu_op;
            tree_valid[0][0] <= valid_in;
        end
    end

    genvar level, lane, pipe;
    generate
        for (level = 0; level < TREE_DEPTH; level++) begin : gen_level
            localparam NUM_ALUS = LANES >> (level + 1);

            // Instantiate ALUs for this tree level
            for (lane = 0; lane < NUM_ALUS; lane++) begin : gen_alu
                vreduction_alu_if vralu_if ();

                // Connect inputs from stage 0 of this level
                assign vralu_if.value_a = tree_data[level][0][2*lane];
                assign vralu_if.value_b = tree_data[level][0][2*lane + 1];
                assign vralu_if.alu_op  = tree_op[level][0];

                vreduction_alu alu_inst (
                    .CLK(CLK),
                    .nRST(nRST),
                    .vraluif(vralu_if.vralu)
                );

                // Capture output to next tree level, stage 0
                always_ff @(posedge CLK or negedge nRST) begin
                    if (!nRST)
                        tree_data[level+1][0][lane] <= '0;
                    else
                        tree_data[level+1][0][lane] <= vralu_if.value_out;
                end
            end

            // Pipeline valid and op through ALU_LATENCY stages
            for (pipe = 1; pipe <= ALU_LATENCY; pipe++) begin : gen_pipe
                always_ff @(posedge CLK or negedge nRST) begin
                    if (!nRST) begin
                        tree_op[level][pipe]   <= 2'b0;
                        tree_valid[level][pipe] <= 1'b0;
                    end else begin
                        tree_op[level][pipe]   <= tree_op[level][pipe-1];
                        tree_valid[level][pipe] <= tree_valid[level][pipe-1];
                    end
                end
            end

            // Transfer valid/op from end of this level to start of next level
            always_ff @(posedge CLK or negedge nRST) begin
                if (!nRST) begin
                    tree_op[level+1][0]   <= 2'b0;
                    tree_valid[level+1][0] <= 1'b0;
                end else begin
                    tree_op[level+1][0]   <= tree_op[level][ALU_LATENCY];
                    tree_valid[level+1][0] <= tree_valid[level][ALU_LATENCY];
                end
            end
        end
    endgenerate

    // Output from final tree level
    assign data_out  = tree_data[TREE_DEPTH][0][0];
    assign valid_out = tree_valid[TREE_DEPTH][0];

endmodule