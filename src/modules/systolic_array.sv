`include "systolic_array_if.vh"
`include "systolic_array_control_unit_if.vh"
`include "systolic_array_MAC_if.vh"
`include "systolic_array_add_if.vh"
`include "systolic_array_FIFO_if.vh"
`include "systolic_array_OUT_FIFO_if.vh"

module systolic_array #(
    parameter N = 4,    // Default dimension of the systolic array
    parameter WIDTH = 16       // Default data width
)(
    input logic clk, nRST,
    systolic_array_if.memory_array memory
);
    // Input to systolic array
    logic [WIDTH*N-1:0] top_input;
    logic [WIDTH*N-1:0] weights_input;
    // logic [WIDTH*N-1:0] partial_sums;
    // Load signals within systolic array
    logic [N-1:0] loadi;
    logic [N-1:0] loadw;
    logic [N-1:0] loadps;
    // MAC Unit inputs/outputs latched within systolic array
    logic [WIDTH-1:0] MAC_inputs [N-1:0][N-1:0];
    logic [WIDTH-1:0] MAC_outputs [N-1:0][N-1:0];
    logic [WIDTH-1:0] nxt_MAC_outputs [N-1:0][N-1:0];
    // Partial Sum adder inputs
    logic [WIDTH-1:0] ps_add_inputs [N-1:0];
    // Weight Registers
    logic [WIDTH*N-1:0] weights [N-1:0];

    // Generate variables
    genvar i,j,l,m,n,o,p;

    // Instantiate Control Unit interface
    systolic_array_control_unit_if #(.array_dim(N), .mul_len(2), .add_len(3)) control_unit_if();

    // Instantiate the control unit
    sysarr_control_unit cu_inst(
        .clk(clk),
        .nRST(nRST),
        .cu(control_unit_if.control_unit)
    );

    // Instantiate MAC unit interfaces
    systolic_array_MAC_if #(.data_w(WIDTH)) mac_ifs[N*N-1:0] (); 
    // Instantiate partial sum adder interfaces
    systolic_array_add_if #(.data_w(WIDTH)) add_ifs[N-1:0] (); 
    // Instantiate Input Fifos
    systolic_array_FIFO_if #(.array_dim(N), .data_w(WIDTH)) input_fifos_ifs[N-1:0] (); 
    // Instantiate Partial Fifos
    systolic_array_FIFO_if #(.array_dim(N), .data_w(WIDTH)) ps_fifos_ifs[N-1:0] (); 
    // Instantiate Output Fifos
    systolic_array_OUT_FIFO_if #(.array_dim(N), .data_w(WIDTH)) out_fifos_ifs[N-1:0] (); 
    always_comb begin : control_unit_connections
        control_unit_if.weight_en = memory.weight_en;
        control_unit_if.input_en = memory.input_en;
        control_unit_if.partial_en = memory.partial_en;
        control_unit_if.row_in_en = memory.row_in_en;
        control_unit_if.row_ps_en = memory.row_ps_en;
        memory.fifo_has_space = control_unit_if.fifo_has_space;
    end
    //Selection Muxes for the input bus
    always_comb begin : input_bus_identity
        top_input = '0;
        weights_input = '0; //'{default: '0};
        if (control_unit_if.input_type == 1'b0) begin
            top_input = memory.array_in;
        end else if (control_unit_if.input_type == 1'b1) begin
            weights_input = memory.array_in;
        end
    end
    always_comb begin : load_sel
        loadi = '0;
        loadw = '0;
        loadps = '0;
        if (control_unit_if.input_load == 1'b1) begin
            loadi[control_unit_if.input_row] = 1'b1;
        end
        if (control_unit_if.weight_load == 1'b1) begin
            loadw[control_unit_if.weight_row] = 1'b1;
        end
        if (control_unit_if.partials_load == 1'b1) begin
            loadps[control_unit_if.partials_row] = 1'b1;
        end
    end
    // Weight Registers Generation
    generate
        for (i = 0; i < N; i++) begin
            always_ff @(posedge clk, negedge nRST) begin : weights_registers
                if(nRST == 1'b0)begin
                    weights[i] <= '0;
                end else if (loadw[i] == 1'b1) begin
                    weights[i] <= weights_input;
                end
            end
        end
    endgenerate    
    // Input Fifo Generation
    generate
        for (j = 0; j < N; j++) begin
            sysarr_FIFO i_fifo (
                .clk(clk),
                .nRST(nRST),
                .fifo(input_fifos_ifs[j].FIFO));
            assign input_fifos_ifs[j].load = loadi[j];
            assign input_fifos_ifs[j].shift = control_unit_if.in_fifo_shift[j];
            assign input_fifos_ifs[j].load_values = top_input;
            assign MAC_inputs[j][0] = input_fifos_ifs[j].out;
        end
    endgenerate
    // Partial Sum Generation
    generate
        for (l = 0; l < N; l++) begin
            sysarr_FIFO ps_fifos (
                .clk(clk),
                .nRST(nRST),
                .fifo(ps_fifos_ifs[l].FIFO));
            assign ps_fifos_ifs[l].load = loadps[l];
            assign ps_fifos_ifs[l].shift = control_unit_if.ps_fifo_shift[l];
            assign ps_fifos_ifs[l].load_values = memory.array_in_partials;
            assign ps_add_inputs[l] = ps_fifos_ifs[l].out;
        end
    endgenerate
    // MAC Generation
    integer z,y;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            for (z = 0; z < N; z++)begin
                for (y = 0; y < N; y++)begin
                    MAC_outputs[z][y] <= '0;
                end
            end
        end else if (control_unit_if.MAC_count == (3+2-1))begin //add params later
            MAC_outputs <= nxt_MAC_outputs;
        end 
    end
    generate
        for (m = 0; m < N; m++) begin
            for (n = 0; n < N; n++) begin
                sysarr_MAC mac_inst (
                    .clk(clk),
                    .nRST(nRST),
                    .mac(mac_ifs[m*N + n].MAC)
                );
                assign mac_ifs[m*N + n].start = control_unit_if.MAC_start;
                assign mac_ifs[m*N + n].count = control_unit_if.MAC_count;
                assign mac_ifs[m*N + n].weight = weights[n][(N - m) * WIDTH - 1 -: WIDTH];
                assign mac_ifs[m*N + n].in_value = MAC_inputs[m][n];
                assign mac_ifs[m*N + n].MAC_shift = control_unit_if.MAC_shift;
                if (m == 0) begin : no_accumulate
                    assign mac_ifs[m*N + n].in_accumulate = '0;
                end else begin : accumulation_blk
                    assign mac_ifs[m*N + n].in_accumulate = MAC_outputs[m-1][n];
                end
                if (n != 0)begin : macInputForwarding
                    assign MAC_inputs[m][n] = mac_ifs[m*N + (n-1)].in_pass;
                end
                assign nxt_MAC_outputs[m][n] = mac_ifs[m*N + n].out_accumulate;
            end
        end
    endgenerate
    // Partial Sum Output Adders Generation
    generate
        for (o = 0; o < N; o++) begin
            sysarr_add add_inst (
                .clk(clk),
                .nRST(nRST),
                .adder(add_ifs[o].add)
            );
            assign add_ifs[o].start = control_unit_if.add_start;
            assign add_ifs[o].count = control_unit_if.add_count;
            assign add_ifs[o].add_input1 = ps_add_inputs[o];
            assign add_ifs[o].add_input2 = MAC_outputs[N-1][o];
        end
    endgenerate
    // Output Fifo Generation
    logic [$clog2(N)-1:0] row_out;
    logic [N-1:0][WIDTH*N-1:0] current_out;
    generate
        for (p = 0; p < N; p++) begin
            sysarr_OUT_FIFO o_fifo (
                .clk(clk),
                .nRST(nRST),
                .out_fifo(out_fifos_ifs[p].OUT_FIFO));
                
            assign out_fifos_ifs[p].shift = control_unit_if.out_fifo_shift;
            assign out_fifos_ifs[p].shift_value = add_ifs[p].add_ouput;
            assign current_out[p] = out_fifos_ifs[p].out;
        end
    endgenerate
    // output time :D
    integer q;

    always_comb begin
        memory.out_en = 1'b0;
        memory.row_out = '0;
        memory.drained = 1'b1;
        row_out = '0;
        memory.array_output = '0;
        for (q = 0; q < 3; q++)begin
            if (control_unit_if.iteration[q] >= 2*N && control_unit_if.add_count == 3)begin //first output done at 2*N then one for every iteration until it is done
                /* verilator lint_off WIDTHTRUNC */
                row_out = control_unit_if.iteration[q] - 2 * N;
                /* verilator lint_off WIDTHTRUNC */
                memory.out_en = 1'b1;
                memory.row_out = row_out;
                memory.array_output = current_out[row_out];
            end
            if (control_unit_if.iteration[q] > 0)begin
                assign memory.drained = 1'b0;
            end
        end
    end
endmodule

