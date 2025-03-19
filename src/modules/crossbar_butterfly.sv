module crossbar_butterfly #(
    parameter N_SIZE     = 4,
    parameter DATA_WIDTH = 32,
    parameter FIFO_SIZE  = 2,
    parameter STAGES     = $clog2(N_SIZE)
) ( 
    input logic CLK, nRST, 
    input logic [N_SIZE-1:0][DATA_WIDTH-1:0] input_vector, 
    input logic [N_SIZE-1:0][STAGES:0] route_mask, // Holds output port index
    output logic [N_SIZE-1:0][DATA_WIDTH-1:0] output_vector, 
    output logic stall 
); 

    logic [N_SIZE-1:0] stall_bus, pop_bus; 
    logic [N_SIZE-1:0][DATA_WIDTH-1:0] arbiter_input; 
    logic [N_SIZE-1:0][STAGES-1:0] arbiter_router_mask;

    logic [N_SIZE-1:0][DATA_WIDTH-1:0] arbiter_data_out;
    logic [N_SIZE-1:0][STAGES-1:0] arbiter_route_out;

    logic [STAGES:0][N_SIZE-1:0][DATA_WIDTH-1:0] stage_data;
    logic [STAGES:0][N_SIZE-1:0][STAGES-1:0] stage_route;

    logic grant; 
    genvar i, j, k, s, p;

    assign stall = |stall_bus; 
    assign output_vector = stage_data[STAGES];
    assign stage_data[0] = arbiter_data_out;
    assign stage_route[0] = arbiter_route_out;

    generate : input_fifos
        for (i = 0; i < N_SIZE; i = i + 1) begin : fifo_inst
            fifo #(
                .DATA_WIDTH(DATA_WIDTH + STAGES),
                .FIFO_SIZE(FIFO_SIZE)
            ) _input_buffer_i ( 
                .CLK(CLK), 
                .nRST(nRST), 
                .input({input_vector[i], route_mask[i]}), 
                .push(1'b1), 
                .pop(pop_bus[i]), 
                .output({arbiter_input[i], arbiter_router_mask[i]}), 
                .stall(stall_bus[i])
            ); 
        end
    endgenerate

    always_comb begin : arbitrator_logic
        integer ii, jj;
        arbiter_data_out = '0;
        arbiter_route_out = '0;
        pop_bus = '0;
        for (jj = 0; jj < N_SIZE; jj = jj + 1) begin
            grant = 0;
            for (ii = 0; ii < N_SIZE; ii = ii + 1) begin
                if (!grant && (arbiter_router_mask[ii] == jj)) begin
                    arbiter_data_out[ii]  = arbiter_input[ii];
                    arbiter_route_out[ii] = arbiter_router_mask[ii];
                    pop_bus[ii] = 1'b1;
                    grant = 1;
                end
            end
        end
    end

    generate : butterflies
        for (s = 0; s < STAGES; s = s + 1) begin : stages
            // each butterfly acts on 2 values
            for (p = 0; p < N_SIZE/2; p = p + 1) begin : pair_switches
                localparam int idx0 = 2 * p;
                localparam int idx1 = 2 * p + 1;
                butterfly_switch #(.DATA_WIDTH(DATA_WIDTH))
                  bs (
                    .in0(stage_data[s][idx0]),
                    .in1(stage_data[s][idx1]),
                    .control(stage_route[s][idx0][s]),
                    .out0(stage_data[s+1][idx0]),
                    .out1(stage_data[s+1][idx1])
                  );
                assign stage_route[s+1][idx0] = stage_route[s][idx0];
                assign stage_route[s+1][idx1] = stage_route[s][idx1];
            end
        end
    endgenerate

endmodule
