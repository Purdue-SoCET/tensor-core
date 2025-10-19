module benes_network #(
    parameter int SIZE = 32,
    parameter int DWIDTH = 16,
    localparam int TAGWIDTH = $clog2(SIZE),
    localparam int STAGES = (2 * TAGWIDTH) - 1
) (
    input logic CLK, nRST,
    input logic [15:0] in [31:0],
    input logic [143:0] control_bit,
    output logic [15:0] out [31:0] 
);

    logic [DWIDTH-1:0] out_latch [STAGES-1:0][SIZE-1:0];
    logic [DWIDTH-1:0] in_latch [STAGES-1:0][SIZE-1:0];

    assign in_latch[0] = in;
    assign out = in_latch[STAGES-1];

    always_ff @( posedge CLK or negedge nRST) begin : blockName
        if (!nRST) begin
            for (int s = 0; s < STAGES; s++) begin
                for (int i = 0; i < SIZE/2; i++) begin
                    in_latch[s][i] <= '0;
                end
            end
        end
        else begin
            for (int s = 0; s < STAGES-1; s++) begin
                for (int i = 0; i < SIZE; i++) begin
                    in_latch[s+1][i] <= out_latch[s][i];
                end
            end
        end
    end

    generate
        genvar i, j, k, l;

        for(i = 0; i < STAGES; i++) begin
            // stage 1 & 9
            if (i == 0 || i == (STAGES - 1) ) begin
                for(j = 0; j < SIZE; j += 2) begin : stage_first_last
                    localparam int ctrl = i / 2;
                    assign out_latch[i][j] = (~control_bit[ctrl]) ? in_latch[j] : in_latch[j + 1];
                    assign out_latch[i][j + 1] = (~control_bit[ctrl]) ? in_latch[j + 1] : in_latch[j];
                end
            end

            else begin
                localparam int d = i > (TAGWIDTH-1) ? i - (TAGWIDTH-1) : (TAGWIDTH-1) - i;
                for (k = 0; k < (1 << d); k++) begin : stage_middle
                    localparam int base_idx = k * (1 << (TAGWIDTH - d));      // starting index for this group
                    localparam int ctrl_adj = ((SIZE/2) * i) - ((TAGWIDTH-1) - d) * k; // offset adjustment per group

                    for (l = 0; l < (1 << (TAGWIDTH-1-d)); l++) begin : pair
                        localparam int idx  = base_idx + l;      // wire index
                        localparam int ctrl = idx + ctrl_adj;    // control bit index

                        assign out_latch[i][idx]                            = (~control_bit[ctrl]) ? in_latch[i][idx]     : in_latch[i][idx + (1 << (TAGWIDTH-1-d))];
                        assign out_latch[i][idx + (1 << (TAGWIDTH-1-d))]    = (~control_bit[ctrl]) ? in_latch[i][idx + (1 << (TAGWIDTH-1-d))] : in_latch[i][idx];
                    end
                end
            end
        end

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
        // for(i = 0; i < 16; i = i + 1) begin : stage_5
        //     localparam int ctrl = (i) + 64;
        //     assign out_5[i] = (~control_bit[ctrl]) ? in_5[i] : in_5[i + 16];
        //     assign out_5[i + 16] = (~control_bit[ctrl]) ? in_5[i + 16] : in_5[i];
        // end

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
    endgenerate


    
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