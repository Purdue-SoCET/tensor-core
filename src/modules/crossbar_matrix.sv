module crossbar #(
    parameter N_SIZE = 4,
    parameter DATA_WIDTH = 32,
    parameter FIFO_SIZE = 2,
    parameter ROUTE_BITS = $clog2(N_SIZE)
) ( 
    input logic CLK, nRST, 
    input logic [N_SIZE-1:0][DATA_WIDTH-1:0] input_vector, 
    input logic [N_SIZE-1:0][ROUTE_BITS:0] route_mask, 
    output logic [N_SIZE-1:0][DATA_WIDTH-1:0] output_vector, 
    output logic stall 
); 

    logic [N_SIZE-1:0] stall_bus, enable_bus, pop_bus; 
    logic [N_SIZE-1:0][DATA_WIDTH-1:0] arbiter_input; 
    logic [N_SIZE-1:0][ROUTE_BITS:0] arbiter_router_mask;
    logic grant;
    genvar i, j, k;

    assign stall = |stall_bus; 

    generate : input_fifos
        fifo (
            .DATA_WIDTH(DATA_WIDTH + ROUTE_BITS), 
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
    endgenerate


    generate : tri_state_matrix
        for (j = 0; j < N; j = j + 1) begin 
            logic [DATA_WIDTH-1:0] bus_j; 
            for (k = 0; k < N; k = k + 1) begin 
                tri_state_buffer #(.DATA_WIDTH(DATA_WIDTH)) _tsb_i_j (
                    .in_data(arbiter_input[k]),
                    .enable(enable_bus[k][j]),
                    .out_data(bus_j)
                );
            end
            assign output_vector[j] = bus_j; 
        end
    endgenerate

    always_comb begin : arbitrator_logic
        integer ii, jj;
        pop_bus = '0; 
        enable_bus = '0; 

        for (jj = 0; jj < N_SIZE; jj = jj + 1) begin
            grant = 0;
            for (ii = 0; ii < N_SIZE; ii = ii + 1) begin
                if (!grant && (arbiter_router_mask[ii] == jj)) begin
                    enable_bus[ii][jj] = 1'b1;
                    pop_bus[ii] = 1'b1; 
                    grant = 1;
                end
            end
        end
    end

endmodule 