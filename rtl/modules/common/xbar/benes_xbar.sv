/*  Haejune Kwon - kwon196@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_params.svh"
`include "xbar_if.sv"

module benes_xbar #(
    parameter int SIZE = 32,
    parameter int DWIDTH = 16, 
    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (2 * TAGWIDTH) - 1
) (
    xbar_if.xbar xif, 
    logic control_bit [STAGES][(SIZE >> 1)]
);


    logic [DWIDTH-1:0] out_latch [STAGES][SIZE];
    logic [DWIDTH-1:0] in_latch [STAGES][SIZE];
    
    always_ff @(posedge xif.clk, negedge xif.n_rst) begin : blockName
        if (!xif.n_rst) begin
            for (int s = 1; s < STAGES; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    in_latch[s][i] <= 16'b0;
                end
            end
        end
        else begin
            for (int s = 1; s < STAGES; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    in_latch[s] <= out_latch[s-1];
                end
            end
        end
    end

    generate
        genvar stage, j, group, l;

        for(stage = 0; stage < STAGES; stage++) begin
            // stage 1
            if (stage == 0) begin
                for(j = 0; j < SIZE; j += 2) begin : stage_first
                    localparam int ctrl = j / 2;
                    crossover_switch #(.SIZE(DWIDTH)) u_less_comp (
                        .din({xif.in[i].din[j], xif.in[i].din[j + 1]}),
                        .cntrl(control_bit[ctrl]), 
                        .dout({out_latch[0][j], out_latch[0][j + 1]})
                    );
                end
            end

            // stage 9
            else if (stage == (STAGES - 1) ) begin
                for(j = 0; j < SIZE; j += 2) begin : stage_last
                    localparam int ctrl = j / 2;
                    crossover_switch #(.SIZE(DWIDTH)) u_less_comp (
                        .din({in_latch[stage][j], in_latch[stage][j + 1]}),
                        .cntrl(control_bit[ctrl]), 
                        .dout({out_latch[stage][j], out_latch[stage][j + 1]})
                    );
                end
            end

            else begin
                localparam int d = stage > (TAGWIDTH-1) ? stage - (TAGWIDTH-1) : (TAGWIDTH-1) - stage;
                for (group = 0; group < (1 << d); group++) begin : stage_middle
                    localparam int base_idx = group * (1 << (TAGWIDTH - d));      // starting index for this group
                    localparam int ctrl_adj = ((SIZE/2) * stage) - ((TAGWIDTH-1) - d) * group; // offset adjustment per group

                    for (j = 0; j < (1 << (TAGWIDTH-1-d)); j++) begin : pair
                        localparam int idx  = base_idx + j;      // wire index
                        localparam int ctrl = idx + ctrl_adj;    // control bit index

                        crossover_switch #(.SIZE(DWIDTH)) u_less_comp (
                            .din({in_latch[stage][idx], in_latch[stage][idx + (1 << (TAGWIDTH-1-d))]}),
                            .cntrl(control_bit[ctrl]), 
                            .dout({out_latch[stage][idx], out_latch[stage][idx + (1 << (TAGWIDTH-1-d))]})
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