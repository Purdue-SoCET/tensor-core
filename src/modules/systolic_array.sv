`include "systolic_array_if.vh"
`include "systolic_array_control_unit_if.vh"
`include "systolic_array_MAC_if.vh"
`include "systolic_array_add_if.vh"
`include "systolic_array_FIFO_if.vh"
`include "systolic_array_OUT_FIFO_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */


module systolic_array(
    input logic clk, nRST,
    systolic_array_if.memory_array memory
);
    // Input to systolic array
    logic [DW*N-1:0] top_input;
    // logic [DW*N-1:0] weights_input;
    // logic [DW*N-1:0] partial_sums;
    // Load signals within systolic array
    logic [N-1:0] loadi;
    // logic [N-1:0] loadw;
    logic [N-1:0] loadps;
    // MAC Unit inputs/outputs latched within systolic array
    logic [DW-1:0] MAC_inputs [N-1:0][N-1:0];
    logic weight_enables [N-1:0] [N-1:0];
    logic [DW-1:0] MAC_outputs [N-1:0][N-1:0];
    logic [DW-1:0] nxt_MAC_outputs [N-1:0][N-1:0];
    // Partial Sum adder inputs
    logic [DW-1:0] ps_add_inputs [N-1:0];
    logic start;
    logic nxt_start;
    logic nxt_drained;

    // Generate variables
    genvar /*i,*/j,l,m,n,o,p;

    // Instantiate Control Unit interface    always_comb begin

    systolic_array_control_unit_if control_unit_if();

    // Instantiate the control unit
    sysarr_control_unit cu_inst(
        .clk(clk),
        .nRST(nRST),
        .cu(control_unit_if.control_unit)
    );

    // Instantiate MAC unit interfaces
    systolic_array_MAC_if mac_ifs[N*N-1:0] (); 
    // Instantiate partial sum adder interfaces
    systolic_array_add_if add_ifs[N-1:0] (); 
    // Instantiate Input Fifos
    systolic_array_FIFO_if input_fifos_ifs[N-1:0] (); 
    // Instantiate Partial Fifos
    systolic_array_FIFO_if ps_fifos_ifs[N-1:0] (); 
    // Instantiate Output Fifos
    systolic_array_OUT_FIFO_if out_fifos_ifs[N-1:0] (); 
    always_comb begin : control_unit_connections
        control_unit_if.weight_en = memory.weight_en;
        control_unit_if.input_en = memory.input_en;
        control_unit_if.partial_en = memory.partial_en;
        control_unit_if.row_in_en = memory.row_in_en;
        control_unit_if.row_ps_en = memory.row_ps_en;
        memory.fifo_has_space = control_unit_if.fifo_has_space;
    end
    //Selection Muxes for the input bus
    assign top_input = memory.array_in;                  // Temporarily bypassing inputs/weights bus selection to test loading weights into MAC units directly
    // always_comb begin : input_bus_identity
    //     top_input = '0;
    //     weights_input = '0; //'{default: '0};
    //     if (control_unit_if.input_type == 1'b0) begin
    //         top_input = memory.array_in;
    //     end else if (control_unit_if.input_type == 1'b1) begin
    //         weights_input = memory.array_in;
    //     end
    // end
    always_comb begin : load_sel
        loadi = '0;
        // loadw = '0;
        loadps = '0;
        if (control_unit_if.input_load == 1'b1) begin
            loadi[control_unit_if.input_row] = 1'b1;
        end
        // if (control_unit_if.weight_load == 1'b1) begin
        //     loadw[control_unit_if.weight_row] = 1'b1;
        // end
        if (control_unit_if.partials_load == 1'b1) begin
            loadps[control_unit_if.partials_row] = 1'b1;
        end
    end
    // Weight Registers Generation
    // generate
    //     for (i = 0; i < N; i++) begin
    //         always_ff @(posedge clk, negedge nRST) begin : weights_registers
    //             if(nRST == 1'b0)begin
    //                 weights[i] <= '0;
    //             end else if (loadw[i] == 1'b1) begin
    //                 weights[i] <= weights_input;
    //             end
    //         end
    //     end
    // endgenerate    
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
            assign MAC_inputs[j][0] = memory.weight_en ? memory.array_in[((N-j)*DW)-1 : ((N-j-1)*DW)] : input_fifos_ifs[j].out;
            assign weight_enables[j][0] = memory.weight_en;
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
        end else if (control_unit_if.MAC_value_ready == 1'b1)begin //add params later
            MAC_outputs <= nxt_MAC_outputs;
        end 
    end
    generate
        for (m = 0; m < N; m++) begin
            for (n = 0; n < N; n++) begin
                sysarr_MAC mac_inst (
                    .clk(clk),
                    .nRST(nRST),
                    .mac_if(mac_ifs[m*N + n].MAC)
                );
                if (m==0 && n==0) begin : mac_ready
                    assign control_unit_if.MAC_value_ready = mac_ifs[m*N + n].value_ready;
                end
                assign mac_ifs[m*N + n].start = control_unit_if.MAC_start;
                // assign mac_ifs[m*N + n].weight = weights[n][(N - m) * DW - 1 -: DW];
                // assign mac_ifs[m*N + n].weight_en = memory.weight_en;
                assign mac_ifs[m*N + n].in_value = MAC_inputs[m][n];
                assign mac_ifs[m*N + n].weight_en = weight_enables[m][n];
                assign mac_ifs[m*N + n].MAC_shift = control_unit_if.MAC_shift;
                if (m == 0) begin : no_accumulate
                    assign mac_ifs[m*N + n].in_accumulate = '0;
                end else begin : accumulation_blk
                    assign mac_ifs[m*N + n].in_accumulate = MAC_outputs[m-1][n];
                end
                if (n != 0)begin : macInputForwarding
                    assign MAC_inputs[m][n] = mac_ifs[m*N + (n-1)].in_pass;
                    assign weight_enables[m][n] = mac_ifs[m*N + (n-1)].weight_next_en;
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
                .adder(add_ifs[o].add)//weights
            );
            if (o == 0) begin : add_ready
                assign control_unit_if.add_value_ready = add_ifs[o].value_ready;
            end
            assign add_ifs[o].start = control_unit_if.add_start;
            assign add_ifs[o].add_input1 = ps_add_inputs[o];
            assign add_ifs[o].add_input2 = MAC_outputs[N-1][o];
        end
    endgenerate
    // Output Fifo Generation
    logic [$clog2(N)-1:0] row_out;
    logic [N-1:0][DW*N-1:0] current_out;
    generate
        for (p = 0; p < N; p++) begin
            sysarr_OUT_FIFO o_fifo (
                .clk(clk),
                .nRST(nRST),
                .out_fifo(out_fifos_ifs[p].OUT_FIFO));
                
            assign out_fifos_ifs[p].shift = control_unit_if.out_fifo_shift;
            assign out_fifos_ifs[p].shift_value = add_ifs[p].add_output;
            assign current_out[p] = out_fifos_ifs[p].out;
        end
    endgenerate
    // output time :D
    integer q;
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            memory.drained <= 1'b1;
            start <= 1'b1;
        end else begin
            memory.drained <= nxt_drained && (control_unit_if.MAC_value_ready || start);
            start <= nxt_start;
        end 
    end
    always_comb begin
        nxt_start = start;
        if (memory.input_en)begin
            nxt_start = 1'b0;
        end
    end
    always_comb begin
        memory.out_en = 1'b0;
        memory.row_out = '0;
        nxt_drained = 1'b1;
        row_out = '0;
        memory.array_output = '0;
        for (q = 0; q < 3; q++)begin
            if (control_unit_if.iteration[q] >= 2*N && control_unit_if.MAC_value_ready == 1'b1)begin //first output done at 2*N then one for every iteration until it is done
                /* verilator lint_off WIDTHTRUNC */
                row_out = control_unit_if.iteration[q] - 2 * N;
                /* verilator lint_off WIDTHTRUNC */
                memory.out_en = 1'b1;
                memory.row_out = row_out;
                memory.array_output = current_out[row_out];
            end
            if (control_unit_if.iteration[q] > 0)begin
                nxt_drained = 1'b0;
            end
        end
    end
endmodule
