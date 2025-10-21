/*  Haejune Kwon - kwon196@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "xbar_params.svh"
`include "xbar_if.sv"
`include "crossover_switch.sv"

module benes_xbar #(
    parameter int SIZE = 32,
    parameter int DWIDTH = 16
) (xbar_if.xbar xif);

    logic [DWIDTH-1:0] out_latch [STAGES-1:0][SIZE-1:0];
    logic [DWIDTH-1:0] in_latch [STAGES-1:0][SIZE-1:0];
    
    assign out = out_latch[8];
    // assign out = out_latch[1];

    always_ff @( posedge CLK, negedge nRST) begin : blockName
        if (!nRST) begin
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
                        .din({in[j], in[j + 1]}),
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
        // // stage 1
        // for(i = 0; i < 32; i = i + 2) begin : stage_1
        // localparam int ctrl = i / 2;
        //     assign out_1[i] = (~control_bit[ctrl]) ? in[i] : in[i + 1];
        //     assign out_1[i + 1] = (~control_bit[ctrl]) ? in[i + 1] : in[i];
        // end

        
        // // stage 3
        // for (g = 0; g < 4; g++) begin : stage_3
        //     localparam int base_idx = g * 8;      // starting index for this group
        //     localparam int ctrl_adj = 32 - 4*g; // offset adjustment per group

        //     for (i = 0; i < 4; i++) begin : pair
        //         localparam int idx  = base_idx + i;      // wire index
        //         localparam int ctrl = idx + ctrl_adj;    // control bit index

        //         assign out_3[idx]     = (~control_bit[ctrl]) ? in_3[idx]     : in_3[idx + 4];
        //         assign out_3[idx + 4] = (~control_bit[ctrl]) ? in_3[idx + 4] : in_3[idx];
        //     end
        // end


        // // stage 4
        // for (g = 0; g < 2; g++) begin : stage_4
        //     localparam int base_idx = g * 16;      // starting index for this group
        //     localparam int ctrl_adj = 48 - 8*g; // offset adjustment per group

        //     for (i = 0; i < 8; i++) begin : pair
        //         localparam int idx  = base_idx + i;      // wire index
        //         localparam int ctrl = idx + ctrl_adj;    // control bit index

        //         assign out_4[idx]     = (~control_bit[ctrl]) ? in_4[idx]     : in_4[idx + 8];
        //         assign out_4[idx + 8] = (~control_bit[ctrl]) ? in_4[idx + 8] : in_4[idx];
        //     end
        // end

        // // stage 5
        // for (g = 0; g < 1; g++) begin : stage_5
        //     localparam int base_idx = g * 32;      // starting index for this group
        //     localparam int ctrl_adj = 64 - 16*g; // offset adjustment per group

        //     for (i = 0; i < 8; i++) begin : pair
        //         localparam int idx  = base_idx + i;      // wire index
        //         localparam int ctrl = idx + ctrl_adj;    // control bit index

        //         assign out_4[idx]     = (~control_bit[ctrl]) ? in_4[idx]     : in_4[idx + 8];
        //         assign out_4[idx + 8] = (~control_bit[ctrl]) ? in_4[idx + 8] : in_4[idx];
        //     end
        // end

        // // stage 6
        // for (g = 0; g < 2; g++) begin : stage_6
        //     localparam int base_idx = g * 16;      // starting index for this group
        //     localparam int ctrl_adj = 80 - 8*g; // offset adjustment per group

        //     for (i = 0; i < 8; i++) begin : pair
        //         localparam int idx  = base_idx + i;      // wire index
        //         localparam int ctrl = idx + ctrl_adj;    // control bit index

        //         assign out_6[idx]     = (~control_bit[ctrl]) ? in_6[idx]     : in_6[idx + 8];
        //         assign out_6[idx + 8] = (~control_bit[ctrl]) ? in_6[idx + 8] : in_6[idx];
        //     end
        // end

        // // stage 7
        // for (g = 0; g < 4; g++) begin : stage_7
        //     localparam int base_idx = g * 8;      // starting index for this group
        //     localparam int ctrl_adj = 96 - 4*g; // offset adjustment per group

        //     for (i = 0; i < 4; i++) begin : pair
        //         localparam int idx  = base_idx + i;      // wire index
        //         localparam int ctrl = idx + ctrl_adj;    // control bit index

        //         assign out_7[idx]     = (~control_bit[ctrl]) ? in_7[idx]     : in_7[idx + 4];
        //         assign out_7[idx + 4] = (~control_bit[ctrl]) ? in_7[idx + 4] : in_7[idx];
        //     end
        // end

        // // stage 8
        // for (g = 0; g < 8; g++) begin : stage_8
        //     localparam int base_idx = g * 4;      // starting index for this group
        //     localparam int ctrl_adj = 112 - 2*g; // offset adjustment per group

        //     for (i = 0; i < 2; i++) begin : pair
        //         localparam int idx  = base_idx + i;      // wire index
        //         localparam int ctrl = idx + ctrl_adj;    // control bit index

        //         assign out_8[idx]     = (~control_bit[ctrl]) ? in_8[idx]     : in_8[idx + 2];
        //         assign out_8[idx + 2] = (~control_bit[ctrl]) ? in_8[idx + 2] : in_8[idx];
        //     end
        // end

        // // stage 9
        // for(i = 0; i < 32; i = i + 2) begin : stage_9
        //     localparam int ctrl = (i / 2) + 128;
        //     assign out[i] = (~control_bit[ctrl]) ? in_9[i] : in_9[i + 1];
        //     assign out[i + 1] = (~control_bit[ctrl]) ? in_9[i + 1] : in_9[i];
        // end
    


    
    // always_ff begin
        // if(~nRST) begin
        //     in_2 <= '{default: 16'b0};
        //     in_3 <= '{default: 16'b0};
        //     in_4 <= '{default: 16'b0};
        //     in_5 <= '{default: 16'b0};
        //     in_6 <= '{default: 16'b0};
        //     in_7 <= '{default: 16'b0};
        //     in_8 <= '{default: 16'b0};
        //     in_9 <= '{default: 16'b0};
        // end
        // else begin
        //     in_2 <= out_1;
        //     in_3 <= out_2;
        //     in_4 <= out_3;
        //     in_5 <= out_4;
        //     in_6 <= out_5;
        //     in_7 <= out_6;
        //     in_8 <= out_7;
        //     in_9 <= out_8;
        // end
    // end
endmodule