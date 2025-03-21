module crossbar_butterfly #(
    parameter N_SIZE     = 4,
    parameter DATA_WIDTH = 32,
    parameter FIFO_SIZE  = 2,
    parameter STAGES = $clog2(N_SIZE),
    parameter ROUTE_BITS = $clog2(N_SIZE)
) ( 
    input logic CLK, nRST, 
    input logic [N_SIZE-1:0][DATA_WIDTH-1:0] input_vector, 
    input logic [N_SIZE-1:0][ROUTE_BITS:0] route_mask, // Holds output port index
    output logic [N_SIZE-1:0][DATA_WIDTH-1:0] output_vector, 
    output logic stall 
); 

    logic [N_SIZE-1:0] stall_bus, pop_bus; 
    logic [N_SIZE-1:0][DATA_WIDTH-1:0] arbiter_input; 
    logic [N_SIZE-1:0][ROUTE_BITS-1:0] arbiter_router_mask;

    logic [N_SIZE-1:0][DATA_WIDTH-1:0] arbiter_data_out;
    logic [N_SIZE-1:0][ROUTE_BITS-1:0] arbiter_route_out;

    logic [STAGES:0][N_SIZE-1:0][DATA_WIDTH-1:0] stage_data;
    logic [STAGES:0][N_SIZE-1:0][ROUTE_BITS-1:0] stage_route;

    logic grant; 
    genvar i, j, k, s, p;

    assign stall = |stall_bus; 

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

    genvar ji;
    generate
        for (ji = 0; ji < N_SIZE; ji = ji + 1) begin : stage_0
            assign stage_data[0][ji] = arbiter_data_out[ji];
            assign stage_route[0][ji] = arbiter_route_out[ji];
        end
    endgenerate

    genvar jk;
    generate
        for (jk = 0; jk < N_SIZE; jk = jk + 1) begin : stage_STAGE
            assign output_vector[jk] = stage_data[STAGES][jk];
        end
    endgenerate

    genvar i, k;
    generate
        for (i = 1; i <= STAGES; i = i + 1) begin : stage_loop
            localparam int flip_val = (1 << (STAGES - i));

            for (k = 0; k < N_SIZE; k = k + 1) begin : switch_inst
                localparam int partner = k ^ flip_val;

                if (k < partner) begin // perform only once per pair
                    wire [DATA_WIDTH-1:0] out0, out1;
                    butterfly_unit #(
                        .DATA_WIDTH(DATA_WIDTH)
                    ) u_butterfly (
                        .in0(stage_data[i-1][k]),
                        .in1(stage_data[i-1][partner];),
                        .control(stage_route[i-1][k][STAGES-1]),
                        .out0(stage_data[i][k]),
                        .out1(stage_data[i][partner])
                    );

                    assign stage_route[i][k] = stage_route[i-1][k] >> 1;
                    assign stage_route[i][partner] = stage_route[i-1][partner] >> 1;

                    initial begin
                        $display("Stage %0d: Instantiated butterfly unit for pair (%0d, %0d)", i, k, partner);
                    end
                end
            end
        end
    endgenerate



endmodule
