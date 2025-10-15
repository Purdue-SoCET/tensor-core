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

    // Pipeline registers
    logic [15:0] stage_data [0:TREE_DEPTH][LANES-1:0];
    logic [1:0]  stage_op   [0:TREE_DEPTH];
    logic        stage_valid[0:TREE_DEPTH];

    // ---------------------------------------------
    // Stage 0: Input register — latch only on valid
    // ---------------------------------------------
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            for (int i = 0; i < LANES; i++)
                stage_data[0][i] <= '0;
            stage_op[0]   <= 2'b0;
            stage_valid[0] <= 1'b0;
        end 
        else if (valid_in) begin
            // Capture new data and control when valid
            for (int i = 0; i < LANES; i++)
                stage_data[0][i] <= data_in[i];
            stage_op[0]   <= alu_op;
            stage_valid[0] <= 1'b1;
        end 
        else begin
            // Hold previous data, mark invalid
            stage_data[0] <= stage_data[0];
            stage_op[0]   <= stage_op[0];
            stage_valid[0] <= 1'b0;
        end
    end

    // --------------------------------------------------
    // Reduction tree pipeline — always shifts forward
    // --------------------------------------------------
    genvar stage, lane;
    generate
        for (stage = 0; stage < TREE_DEPTH; stage++) begin : gen_stage
            localparam STAGE_OUTS = LANES >> (stage + 1);

            for (lane = 0; lane < STAGE_OUTS; lane++) begin : gen_lane
                vreduction_alu_if vralu_if ();

                assign vralu_if.value_a = stage_data[stage][2*lane];
                assign vralu_if.value_b = stage_data[stage][2*lane + 1];
                assign vralu_if.alu_op  = stage_op[stage];

                vreduction_alu alu_inst (
                    .CLK(CLK),
                    .nRST(nRST),
                    .vraluif(vralu_if.vralu)
                );

                // Registered ALU output
                always_ff @(posedge CLK or negedge nRST) begin
                    if (!nRST)
                        stage_data[stage+1][lane] <= '0;
                    else
                        stage_data[stage+1][lane] <= vralu_if.value_out;
                end
            end

            // Shift control signals forward every cycle
            always_ff @(posedge CLK or negedge nRST) begin
                if (!nRST) begin
                    stage_op[stage+1]   <= 2'b0;
                    stage_valid[stage+1] <= 1'b0;
                end else begin
                    stage_op[stage+1]   <= stage_op[stage];
                    stage_valid[stage+1] <= stage_valid[stage];
                end
            end
        end
    endgenerate

    // --------------------------------------------------
    // Final output register
    // --------------------------------------------------
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            data_out  <= '0;
            valid_out <= 1'b0;
        end else begin
            data_out  <= stage_data[TREE_DEPTH][0];
            valid_out <= stage_valid[TREE_DEPTH];
        end
    end

endmodule
