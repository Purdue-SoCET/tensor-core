/*  Haejune Kwon - kwon196@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_params.svh"
`include "xbar_if.sv"

import xbar_pkg::*;

module benes #(
    parameter int SIZE = 32,
    parameter int DWIDTH = 16, 
    parameter logic [7:0] REGISTER_MASK = 8'b11111111,

    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (2 * TAGWIDTH) - 1, 
    localparam int BITWIDTH = STAGES * (SIZE >> 1)
) (
    xbar_if.xbar xif,
    input logic [BITWIDTH-1:0] control_bit 
);

	logic [DWIDTH-1:0] reg_latch [STAGES-1][SIZE]; 
    logic [DWIDTH-1:0] out_latch [STAGES][SIZE];
    logic [DWIDTH-1:0] in_latch [STAGES][SIZE];
    
    always_ff @ (posedge xif.clk, negedge xif.n_rst) begin
        if (!xif.n_rst) begin
            for (int s = 0; s < STAGES-1; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    reg_latch[s][i] <= '0;
                end
            end
        end
        else begin
            for (int s = 0; s < STAGES-1; s++) begin
            	if (REGISTER_MASK[s]) begin 
	                for (int i = 0; i < SIZE; i++) begin
	                    reg_latch[s][i] <= out_latch[s][i];
	                end
	            end 
            end
        end
    end

    generate
    	genvar i, s;

        for (s = 1; s < STAGES; s++) begin 
            for (i = 0; i < SIZE; i++) begin 
                assign in_latch[s][i] = REGISTER_MASK[s-1] ? reg_latch[s-1][i] : out_latch[s-1][i];
            end
        end
    endgenerate

    generate
        genvar stage, j, group;

        for(stage = 0; stage < STAGES; stage++) begin
            // stage 1
            if (stage == 0) begin
                for(j = 0; j < SIZE; j += 2) begin : stage_first
                    localparam int ctrl = j / 2;
                    crossover_switch #(.SIZE(DWIDTH)) u_less_comp (
                        .din({xif.in[j], xif.in[j + 1]}),
                        .cntrl(control_bit[ctrl]), 
                        .dout({out_latch[0][j], out_latch[0][j + 1]})
                    );
                end
            end

            // stage last
            else if (stage == (STAGES - 1) ) begin
                for(j = 0; j < SIZE; j += 2) begin : stage_last
                    localparam int ctrl = ((SIZE/2)*stage) + (j/2);
                    crossover_switch #(.SIZE(DWIDTH)) u_less_comp (
                        .din({in_latch[stage][j], in_latch[stage][j + 1]}),
                        .cntrl(control_bit[ctrl]), 
                        .dout({out_latch[stage][j], out_latch[stage][j + 1]})
                    );
                end
            end

            else begin
                // localparam int d = stage <= (STAGES-1)/2 ? stage : (STAGES-1) - stage;
                localparam int d = (stage < TAGWIDTH) ? (1 << stage) : (1 << (STAGES - 1 - stage));

                for (group = 0; group < (SIZE/2) / d; group++) begin : stage_middle
                    localparam int base_idx = group * (d << 1);      // starting index for this group
                    localparam int ctrl_adj = ((SIZE/2) * stage) - (d * group); // offset adjustment per group

                    for (j = 0; j < d; j++) begin : pair
                        localparam int idx  = base_idx + j;      // wire index
                        localparam int ctrl = idx + ctrl_adj;    // control bit index

                        crossover_switch #(.SIZE(DWIDTH)) u_less_comp (
                            .din({in_latch[stage][idx], in_latch[stage][idx + d]}),
                            .cntrl(control_bit[ctrl]), 
                            .dout({out_latch[stage][idx], out_latch[stage][idx + d]})
                        );
                    end
                end
            end
        end
    endgenerate

    always_comb begin
        for (int i = 0; i < SIZE; i++) begin
            xif.out[i] = out_latch[STAGES-1][i];
        end
    end
    
endmodule