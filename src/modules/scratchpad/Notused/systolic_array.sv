`include "systolic_array_if.vh"
`include "systolic_array_control_unit_if.vh"
`include "systolic_array_MAC_if.vh"
`include "systolic_array_add_if.vh"
`include "systolic_array_FIFO_if.vh"
`include "systolic_array_PS_FIFO_if.vh"

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
    logic [WIDTH*N-1:0] partial_sums;
    // Load signals within systolic array
    logic [N-1:0] loadi;
    logic [N-1:0] loadw;
    logic [N-1:0] loadps;
    // Shift signals for Fifos
    logic [N-1:0] fifo_shift;
    logic [N-1:0] ps_fifo_shift;
    // MAC Unit connections within systolic array
    logic [WIDTH-1:0] MAC_inputs [N-1:0][N-1:0];
    logic [WIDTH-1:0] out_accumulate [N-1:0][N-1:0];
    // Partial Sum adder inputs
    logic [WIDTH-1:0] ps_add_inputs [N-1:0];
    // Weight Registers
    logic [WIDTH*N-1:0] weights [N-1:0];
    // Output Matrix Buffer
    logic [WIDTH-1:0] output_buffer_next [N-1:0][N-1:0];
    logic [WIDTH-1:0] output_buffer [N-1:0][N-1:0];
    // Generate variables
    genvar i,j;

    // Instantiate Control Unit interface
    systolic_array_control_unit_if #(.array_dim(N), .data_w(WIDTH)) control_unit_if();

    // Instantiate the control unit
    control_unit  cu (
        .clk(clk),
        .rst(rst),
        .control_unit(control_unit_if.control_unit)
    );

    // Instantiate MAC unit interfaces
    systolic_array_MAC_if #(.data_w(WIDTH)) mac_ifs[N-1:0][N-1:0] (); 
    // Instantiate partial sum adder interfaces
    systolic_array_add_if #(.data_w(WIDTH)) add_ifs[N-1:0] (); 
    // Instantiate Input Fifos
    systolic_array_fifo_if #(.array_dim(N), .data_w(WIDTH)) input_fifos_ifs[N-1:0] (); 
    // Instantiate Partial Fifos
    systolic_array_ps_fifo_if #(.array_dim(N), .data_w(WIDTH)) ps_fifos_ifs[N-1:0] (); 

    //Selection Muxes for the input bus
    always_comb begin : input_bus_identity
        top_input = '0;
        weights = '{default: '0};
        if (control_unit_if.input_type == 1'b0) begin
            top_input = memory.array_in;
        end else if (control_unit_if.input_type == 1'b1) begin
            weights = memory.array_in;
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
        if (control_unit_if.input_load == 1'b1) begin
            loadps[control_unit_if.partials_row] = 1'b1;
        end
    end
    // Weight Registers Generation
    generate
        for (i = 0; i < N; i = i + 1) begin
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
        for (i = 0; i < N; i = i + 1) begin
            FIFO i_fifo (
                .clk(clk),
                .rst(rst),
                .FIFO(input_fifos_ifs[i].FIFO));
            assign input_fifos_ifs[i].load = loadi[i];
            assign input_fifos_ifs[i].shift = control_unit_if.fifo_shift[i];
            assign input_fifos_ifs[i].load_values = top_input;
            for (j = 0; j < N; j = j + 1) begin
                assign MAC_inputs[i][j] = input_fifos_ifs[i].out[j * WIDTH +: WIDTH];
            end
        end
    endgenerate
    // Partial Sum Generation
    generate
        for (i = 0; i < N; i = i + 1) begin
            PS_FIFO ps_fifo (
                .clk(clk),
                .rst(rst),
                .PS_FIFO(ps_fifos_ifs[i].PS_FIFO));
            assign ps_fifos_ifs[i].load = loadps[i];
            assign ps_fifos_ifs[i].shift = control_unit_if.ps_fifo_shift[i];
            assign ps_fifos_ifs[i].load_values = memory.array_in_partials;
            assign ps_add_inputs[i] = ps_fifos_ifs[i].out;
        end
    endgenerate
    // MAC Generation
    generate
        for (i = 0; i < N; i = i + 1) begin
            for (j = 0; j < N; j = j + 1) begin
                MAC_unit mac_inst (
                    .clk(clk),
                    .rst(rst),
                    .MAC(mac_ifs[i][j].MAC)
                );
                assign mac_ifs[i][j].start = control_unit_if.MAC_start;
                assign mac_ifs[i][j].count = control_unit_if.MAC_count;
                assign mac_ifs[i][j].weight = weights[j][i * WIDTH +: WIDTH];
                assign mac_ifs[i][j].in_value = MAC_inputs[i][j];
                if (i == 0) begin
                    assign mac_ifs[i][j].in_accumulate = '0;
                end else begin
                    assign mac_ifs[i][j].in_accumulate = out_accumulate[i][j-1];
                end
                assign out_accumulate[i][j] = mac_ifs[i][j].out_accumulate;
            end
        end
    endgenerate
    // Partial Sum Output Adders Generation
    generate
        for (i = 0; i < N; i = i + 1) begin
            adder add_inst (
                .clk(clk),
                .rst(rst),
                .add(add_ifs[i].add)
            );
            assign add_ifs[i].start = control_unit_if.add_start;
            assign add_ifs[i].count = control_unit_if.add_count;
            assign add_ifs[i].add_input1 = ps_add_inputs[i];
            assign add_ifs[i].add_input2 = out_accumulate[N-1][i];
            //hard part where to put addifs
            assign output_buffer_next = output_buffer;
            if (control_unit_if.iteration_out > 0) begin
                assign output_buffer_next[i][control_unit_if.iteration_out-1] = add_ifs[i].add_ouput;
            end
        end
    endgenerate

    always_ff @(posedge clk, negedge nRST) begin :outputBuffer
        if(nRST == 1'b0)begin
            output_buffer <= '{default: '0};
        end else begin
            output_buffer <= output_buffer_next;
        end
    end
    // output time :D
    integer k;
    always_comb begin
        for (k = 0; k < 3; k++)begin
            if (control_unit_if.iteration[k] > 2*N-1)begin
                memory.row_out = control_unit_if.iteration[k]-2*N;
                memory.array_output = {output_buffer[memory.row_out]};
            end
        end
    end
endmodule
