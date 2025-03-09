`include "systolic_array_if.vh"
`include "systolic_array_control_unit_if.vh"


module control_unit #(
    parameter N = 4,    // Default dimension of the systolic array
    parameter MUL_LEN = 2,
    parameter ADD_LEN = 3
)(
    input logic clk, nRST,
    systolic_array_control_unit_if.control_unit cu
);

    logic start_flag;
    logic changed_weights;
    logic nxt_changed_weights;
    logic last_MAC;
    // next MAC signals
    logic [$clog2(MUL_LEN+ADD_LEN)-1:0] nxt_MAC_count;
    logic nxt_MAC_start;
    // next add signals
    logic [$clog2(ADD_LEN)-1:0] nxt_add_count;
    logic nxt_add_start;
    // next signals for iterations
    logic [$clog2(N)-1:0] iteration [2:0];    //there can be at most 3 instructions in flight in saturated pipeline
    logic [2:0] iteration_full;             // whether there is an iteration in this slot 001 means an iteration in first slot 
    logic [$clog2(N)-1:0] nxt_iteration [2:0];    //there can be at most 3 instructions in flight in saturated pipeline
    logic [2:0] nxt_iteration_full;             // whether there is an iteration in this slot 001 means an iteration in first slot 
    // we have space for another instruction to start loading in inputs 

    always_comb begin : input_buses // if we are receiving inputs tell the fifos where to load them :D
        cu.input_type = 1'b0; 
        cu.input_row = '0;
        cu.input_load = 1'b0;
        cu.weight_row = '0;
        cu.weight_load = 1'b0;
        cu.partials_row = '0;
        cu.partials_load = 1'b0;
        if (cu.input_en) begin
            cu.input_row = cu.row_en;
            cu.input_load = 1'b1;
        end else if (cu.weight_en) begin
            cu.input_type = 1'b1;
            cu.weight_row = cu.row_en;
            cu.weight_load = 1'b1;
        end
        if (cu.partial_en) begin
            cu.partials_row = cu.row_en;
            cu.partials_load = 1'b1;
        end
    end
    // start an instruction the cycle after the last row of input loads
    assign start_flag = cu.input_en && (cu.row_en == 0);
    // keep track of if the weights were changed in which case we have to have special startup
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            changed_weights <= 1'b1; 
        end else begin
            changed_weights <= nxt_changed_weights;
        end 
    end
    always_comb begin
        nxt_changed_weights = changed_weights;
        if (cu.weight_en) begin
            nxt_changed_weights = 1'b1;
        end
        if (nxt_changed_weights && cu.input_row == N-1) begin //once we are done with startup we can set changed_weights flag back to 0 
            nxt_changed_weights = 1'b0;
        end
    end
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
    integer i;
    always_comb begin
        nxt_iteration = iteration;
        nxt_iteration_full = iteration_full;
        for (i = 0; i < 3; i++)begin // starter for loop to say full
            if (start_flag)begin
                if (iteration_full[i] == 1'b0) begin
                    nxt_iteration_full[i] = 1'b1;
                    break;
                end
            end
        end
        for (i = 0; i < 3; i++)begin // counting logic
            if (iteration_full[i] && nxt_MAC_start)begin // if there is a counter in this slot and a mac cycle is ending
                nxt_iteration[i] = iteration[i] + 1;
                if (iteration[i] == 3*N-1) begin // this iteration is done
                    nxt_iteration[i] = 0;
                    nxt_iteration_full[i] = 0;
                end
            end
        end
    end
    always_comb begin
        cu.fifo_has_space = 1'b0;
        if (&iteration_full == 1'b0)begin
            cu.fifo_has_space = 1'b1;
        end else if(iteration[0] > 2*N || iteration[1] > 2*N || iteration[2] > 2*N)begin // an iteration is fully in the systolic array
            cu.fifo_has_space = 1'b1;
        end
    end
    // fifo shifts and enables
    integer j;
    always_comb begin
        cu.fifo_shift = '0;
        cu.ps_fifo_shift = '0;
        for (j = 0; j < N; j++)begin
            if (nxt_MAC_start) begin                // shift on the start of each MAC cycle
                cu.fifo_shift[j] = 1'b1;
                cu.ps_fifo_shift[j] = 1'b1;
                if (j > cu.input_row && changed_weights) begin     // unless it is on startup
                    cu.fifo_shift[j] = 1'b0;
                    cu.ps_fifo_shift[j] = 1'b0;
                end
            end
        end
    end
    // MAC count
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            cu.MAC_start <= '0;
            cu.MAC_count <= '0;
        end else begin
            cu.MAC_start <= nxt_MAC_start;
            cu.MAC_count <= nxt_MAC_count;
        end 
    end
    always_comb begin
        nxt_MAC_count = cu.MAC_count;
        nxt_MAC_start = 1'b0;
        if (cu.MAC_count > 0 || cu.MAC_start) begin // MAC should be counting
            nxt_MAC_count = cu.MAC_count + 1;
        end
        if (start_flag == 1'b1 || (cu.MAC_count + 1) == (ADD_LEN + MUL_LEN))begin //start or restart count
            nxt_MAC_start = 1'b1;
            nxt_MAC_count = 0;
        end
    end
    // add signals
    always_ff @(posedge clk, negedge nRST) begin
        if(nRST == 1'b0)begin
            cu.add_start <= '0;
            cu.add_count <= '0;
        end else begin
            cu.add_start <= nxt_add_start;
            cu.add_count <= nxt_add_count;
        end 
    end
    integer k;
    always_comb begin
        nxt_add_start = 1'b0;
        nxt_add_count = cu.add_count;
        for (k = 0; k < 3; k++)begin
            if (iteration[k] > 2*N)begin
                nxt_add_start = 1'b1;
            end
        end
        if (cu.add_start || cu.add_count > 0) begin
            nxt_add_count = cu.add_count + 1;
            if (nxt_add_count == ADD_LEN)begin
                nxt_add_count = 0;
            end
        end
    end
endmodule
