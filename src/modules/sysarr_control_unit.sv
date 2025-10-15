`include "systolic_array_control_unit_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */

module sysarr_control_unit(
    input logic clk, 
    input logic nRST,
    input logic stall_sa, //name of the stall signal 
    systolic_array_control_unit_if.control_unit cu
);
    logic start_flag;
    // next MAC signals
    logic nxt_MAC_start;
    // next signals for iterations
    logic [$clog2(3*N)-1:0] iteration [2:0];    //there can be at most 3 instructions in flight in saturated pipeline
    logic [$clog2(3*N)-1:0] nxt_iteration [2:0];
    logic [2:0] iteration_full;             // whether there is an iteration in this slot: 001 means an iteration in first slot 
    logic [2:0] nxt_iteration_full;
    logic input_loading;        // only continue with execution if input row is loaded
    logic [$clog2(N)-1:0] curr_input_row;   // current input row to check
    logic partial_loading;      // only continue with execution if partial row is loaded
    logic [$clog2(N)-1:0] curr_partial_row; // current partial row to check
    logic output_loading;       // we are creating the output 
    logic [N-1:0] in_data_loaded;       // registers for saving what input rows we have loaded so far
    logic [N-1:0] ps_data_loaded;       // registers for saving what partials rows we have loaded so far
    logic [N-1:0] nxt_in_data_loaded;
    logic [N-1:0] nxt_ps_data_loaded;
    logic input_fully_loaded;           // flag for input data fully loaded so we can start tracking the next input
    logic [1:0] partial_fully_loaded;         // flag for partial data fully loaded so we can start tracking the next partials just use count for pipelining guarentees
    logic nxt_input_fully_loaded;
    logic [1:0] nxt_partial_fully_loaded;
    logic first_mac;
    logic nxt_first_mac;
    logic MAC_ready;
    logic nxt_MAC_ready;
    integer a,b,f,i,j,k,l,m,n;
    // we have space for another instruction to start loading in inputs 
    assign cu.iteration = iteration;


    always_comb begin : input_buses // if we are receiving inputs tell the fifos where to load them :D
        // cu.input_type = 1'b0; 
        cu.input_row = '0;
        cu.input_load = 1'b0;
        // cu.weight_row = '0;
        // cu.weight_load = 1'b0;
        cu.partials_row = '0;
        cu.partials_load = 1'b0;
        if (cu.input_en) begin
            cu.input_row = cu.row_in_en;
            cu.input_load = 1'b1;
        end else if (cu.weight_en) begin
            // cu.input_type = 1'b1;
            // cu.weight_row = cu.row_in_en;
            // cu.weight_load = 1'b1;
        end
        if (cu.partial_en) begin
            cu.partials_row = cu.row_ps_en;
            cu.partials_load = 1'b1;
        end
    end
    
    // start an instruction the cycle after the first row of input loads (only need first entry)
    assign start_flag = cu.input_en && (cu.row_in_en == 0) && !stall_sa;

    // iteration tracker
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            iteration <= '{default: '0};
            iteration_full <= '0;
        end else begin
            iteration <= nxt_iteration;
            iteration_full <= nxt_iteration_full;
        end 
    end
    
    // check control unit draw.io
    always_comb begin
        nxt_iteration = iteration;
        nxt_iteration_full = iteration_full;
        for (i = 0; i < 3; i++)begin // starter for loop to say full
            if (start_flag)begin //if an operation is starting make sure to initialize an iteration slot
                if (iteration_full[i] == 1'b0) begin
                    nxt_iteration_full[i] = 1'b1;
                    break;
                end
            end
        end
        // needs to be much more complicated
        for (j = 0; j < 3; j++)begin // iteration counting logic
            if (nxt_iteration_full[j] && nxt_MAC_start)begin // if there is an iteration counter in this slot and a mac cycle is about to start
                nxt_iteration[j] = iteration[j] + 1;
                if (iteration[j] == 3*N-1) begin // this iteration is done
                    nxt_iteration[j] = 0;
                    nxt_iteration_full[j] = 0;
                end
            end
        end
    end
    
    // fifo shifts and enables
    always_comb begin
        cu.in_fifo_shift = '0;
        cu.ps_fifo_shift = '0;
        cu.out_fifo_shift = '0;
        cu.MAC_shift = '0;
        for (f = 0; f < N; f++)begin
            for (a = 0; a < 3; a++) begin
                if (iteration_full[a] && ((f < iteration[a]) && (f + N >= iteration[a])))begin
                    //5,8 0 6,9 1 7,10 2 8,11 3 iteration_start,iteration_end, f
                    cu.in_fifo_shift[f] = nxt_MAC_start;
                end
            end
            // if (output_loading) begin  // shift each  fifo n times
            for (b = 0; b < 3; b++) begin
                if (iteration_full[b] && ((f + N < iteration[b]) && (f + 2 * N >= iteration[b])))begin
                    cu.ps_fifo_shift[f] = nxt_MAC_start;
                end
            end
            // end
        end
        if (|iteration_full)begin
            cu.MAC_shift = cu.MAC_start;
        end
        if (cu.add_value_ready == 1'b1) begin
            cu.out_fifo_shift = 1'b1;
        end
    end
    // MAC 
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            cu.MAC_start <= '0;
            first_mac <= '0;
            MAC_ready <= 1'b1;
        end else begin
            cu.MAC_start <= nxt_MAC_start;
            first_mac <= nxt_first_mac;
            MAC_ready <= nxt_MAC_ready;
        end 
    end

    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            in_data_loaded <= '0;
            ps_data_loaded <= '0;
            input_fully_loaded <= '0;
            partial_fully_loaded <= '0;
        end else begin
            in_data_loaded <= nxt_in_data_loaded;
            ps_data_loaded <= nxt_ps_data_loaded;
            input_fully_loaded <= nxt_input_fully_loaded;
            partial_fully_loaded <= nxt_partial_fully_loaded;
        end 
    end
    always_comb begin
        nxt_in_data_loaded = in_data_loaded;
        nxt_ps_data_loaded = ps_data_loaded;
        nxt_input_fully_loaded = input_fully_loaded;
        nxt_partial_fully_loaded = partial_fully_loaded;
        for (k = 0; k < 3; k++)begin
            if (iteration_full[k])begin
                if (iteration[k] == N && cu.MAC_start)begin
                    nxt_input_fully_loaded = 1'b0;
                end else if (iteration[k] == 2 * N + 1 && cu.MAC_start)begin
                    nxt_partial_fully_loaded -= 1;
                end
            end
        end
        if (cu.input_en) begin
            nxt_in_data_loaded[cu.row_in_en] = 1'b1;
        end
        if (cu.partial_en) begin
            nxt_ps_data_loaded[cu.row_ps_en] = 1'b1;
        end
        if (&nxt_in_data_loaded)begin
            nxt_input_fully_loaded = 1'b1;
            nxt_in_data_loaded = '0;
        end
        if (&nxt_ps_data_loaded)begin
            nxt_partial_fully_loaded += 1;
            nxt_ps_data_loaded = '0;
        end
    end
    always_comb begin // tracks if a gemm is still loading inputs or partial sums
        input_loading = '0;
        curr_input_row = '0;
        partial_loading = '0; 
        curr_partial_row = '0;
        output_loading = '0; 
        for (l = 0; l < 3; l++)begin
            if ((start_flag || iteration_full[l]) && iteration[l] < N)begin
                input_loading = 1'b1;
                /* verilator lint_off WIDTHTRUNC */
                curr_input_row = iteration[l];
                /* verilator lint_off WIDTHTRUNC */
                break;
            end
        end
        for (m = 0; m < 3; m++)begin
            if (iteration_full[m] && iteration[m] <= 2 * N && iteration[m] > N)begin
                partial_loading = 1'b1;
                /* verilator lint_off WIDTHTRUNC */
                curr_partial_row = iteration[m] - (N + 1);
                /* verilator lint_off WIDTHTRUNC */
                break;
            end
        end
        for (n = 0; n < 3; n++)begin
            if (iteration_full[n] && iteration[n] > N)begin
                output_loading = 1'b1;
                break;
            end
        end
    end
    // tells the memory subsystem if the input fifo has space for another gemm
    // if any iteration slot is still in the backend of the fifos then there is no space
    assign cu.fifo_has_space = input_loading == 1'b0 & partial_loading == 1'b0;
    logic fulll /*verilator public*/;

    always_comb begin
        nxt_MAC_start = 1'b0;
        nxt_first_mac = first_mac;
        if (cu.weight_en)begin
            nxt_first_mac = 1'b1;
        end
        nxt_MAC_ready = MAC_ready;
        if (cu.MAC_value_ready == 1'b1)begin
            nxt_MAC_ready = 1'b1;
        end
        fulll = |iteration_full;
        if (|iteration_full && (MAC_ready == 1'b1 || cu.MAC_value_ready))begin
            if (input_loading & partial_loading)begin // an input and partial from two gemms are concurrently loading need to wait for both
                if ((in_data_loaded[curr_input_row] || input_fully_loaded) && (ps_data_loaded[curr_partial_row] || |partial_fully_loaded))begin
                    nxt_MAC_start = 1'b1;
                    nxt_MAC_ready = 1'b0;
                end
            end else if (input_loading)begin // input being loaded
                if(in_data_loaded[curr_input_row] || input_fully_loaded)begin
                    nxt_MAC_start = 1'b1;
                    nxt_MAC_ready = 1'b0;
                end
            end else if (partial_loading)begin //input loaded but waiting for partials add all loaded signal
                if(ps_data_loaded[curr_partial_row] || |partial_fully_loaded)begin
                    nxt_MAC_start = 1'b1;
                    nxt_MAC_ready = 1'b0;
                end
            end else begin // output being produced
                nxt_MAC_start = 1'b1;
                nxt_MAC_ready = 1'b0;
            end
            
        end else if (first_mac == 1'b1 && start_flag)begin
            nxt_MAC_start = 1'b1;
            nxt_first_mac = 1'b0;
            nxt_MAC_ready = 1'b0;
        end
        nxt_MAC_start &= ~stall_sa;
        nxt_MAC_ready |= stall_sa;
    end

    always_comb begin
        cu.add_start = 1'b0;
        if (output_loading && cu.MAC_start)begin
            cu.add_start = 1'b1;
        end
    end
endmodule
