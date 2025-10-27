// 11 bit wallace tree multiplier. Single cycle edition, no pipelining.

// by: Mixuan Pan and Vinay Pundith, September 2025

`timescale 1ns/1ps

// module mul_wallacetree #(parameter num_bits = 11) (input logic clk, nRST, start, stop, input logic [num_bits-1:0] op1, op2, output logic [num_bits-1:0] result, output logic overflow, round_loss);
module wallacetree_11b (input logic [10:0] a, b, output logic [12:0] result, output logic overflow, round_loss);

logic [2:0][12:0] stage1_sums;
logic [2:0][10:0] stage1_carries;

genvar i, j, k, l, n, o, p, q;

generate                                // stage1 levels 1 through 3
    for(i = 0; i < 3; i++)
    begin
        assign stage1_sums[i][0] = a[i*3] & b[0];       // LSB of level's sums array is a0b0 for level1, a3b0 for l2, a6b0 for l3, etc
        assign stage1_sums[i][12] = a[i*3 +2] & b[10];
        
        ha ha_00_first (.a(a[i*3] & b[1]), .b(a[i*3 + 1] & b[0]), .s(stage1_sums[i][1]), .cout(stage1_carries[i][0]));
        ha ha_00_last (.a(a[i*3 + 1] & b[10]), .b(a[i*3 + 2] & b[9]), .s(stage1_sums[i][11]), .cout(stage1_carries[i][10]));
        
            for (j = 2; j <=10; j++)
            begin
                fa fa_00 (.a(a[i*3] & b[j]), .b(a[i*3 +1] & b[j-1]), .cin(a[i*3 + 2] & b[j-2]), .s(stage1_sums[i][j]), .cout(stage1_carries[i][j-1]));
            end

    end
endgenerate

// compression stage2

logic [1:0][12:0] stage2_carries;
logic [1:0][15:0] stage2_sums;

// stage2 level1

// bits 1:0 come straight from stage1
assign stage2_sums[0][1:0] = stage1_sums[0][1:0];

// half adder for bit 2
ha ha_s2_l1_b2 (.a(stage1_sums[0][2]), .b(stage1_carries[0][0]), .s(stage2_sums[0][2]), .cout(stage2_carries[0][0]));

// full adders for bits 3 to 12
generate
    for(k=3; k<=12; k++)
    begin
        fa fa_s2_l1 (.a(stage1_sums[0][k]), .b(stage1_carries[0][k-2]), .cin(stage1_sums[1][k-3]), .s(stage2_sums[0][k]), .cout(stage2_carries[0][k-2]));
    end
endgenerate

//bits 15:13 come straight from stage1
assign stage2_sums[0][15:13] = stage1_sums[1][12:10];

// stage2 level2

// Hard coding bits 
assign stage2_sums[1][0] = stage1_carries[1][0];

ha ha_s2_l2_b1 (.a(stage1_carries[1][1]), .b(stage1_sums[2][0]), .s(stage2_sums[1][1]), .cout(stage2_carries[1][0]));
ha ha_s2_l2_b2 (.a(stage1_carries[1][2]), .b(stage1_sums[2][1]), .s(stage2_sums[1][2]), .cout(stage2_carries[1][1]));
generate
    for(l=3; l <= 10; l++)      // Full adders for bits 3 through 10 of result
    begin
        fa fa_s2_l2 (.a(stage1_carries[1][l]), .b(stage1_sums[2][l-1]), .cin(stage1_carries[2][l-3]), .s(stage2_sums[1][l]), .cout(stage2_carries[1][l-1]));
    end
endgenerate
ha ha_s2_l2_b11 (.a(stage1_sums[2][10]), .b(stage1_carries[2][8]), .s(stage2_sums[1][11]), .cout(stage2_carries[1][10]));
ha ha_s2_l2_b12 (.a(stage1_sums[2][11]), .b(stage1_carries[2][9]), .s(stage2_sums[1][12]), .cout(stage2_carries[1][11]));
ha ha_s2_l2_b13 (.a(stage1_sums[2][12]), .b(stage1_carries[2][10]), .s(stage2_sums[1][13]), .cout(stage2_carries[1][12]));


// stage 3:
logic [18:0] stage3_level1_sums;
logic [13:0] stage3_level2_sums;
logic [1:0][12:0] stage3_carries;

// level 1
// bits 0 to 2 come directly from prev stage
assign stage3_level1_sums[2:0] = stage2_sums[0][2:0];

// half adders for bits 3, 4
ha ha_s3_l1_b3 (.a(stage2_sums[0][3]), .b(stage2_carries[0][0]), .s(stage3_level1_sums[3]), .cout(stage3_carries[0][0]));
ha ha_s3_l1_b4 (.a(stage2_sums[0][4]), .b(stage2_carries[0][1]), .s(stage3_level1_sums[4]), .cout(stage3_carries[0][1]));

// full adders for bits 5 to 13
generate
    for(n = 5; n <=13; n++)
    begin
        fa fa_s3_l1 (.a(stage2_sums[0][n]), .b(stage2_carries[0][n-3]), .cin(stage2_sums[1][n-5]), .s(stage3_level1_sums[n]), .cout(stage3_carries[0][n-3]));
    end
endgenerate

// half adders for bits 14, 15
ha ha_s3_l1_b14 (.a(stage2_sums[0][14]), .b(stage2_sums[1][9]), .s(stage3_level1_sums[14]), .cout(stage3_carries[0][11]));
ha ha_s3_l1_b15 (.a(stage2_sums[0][15]), .b(stage2_sums[1][10]), .s(stage3_level1_sums[15]), .cout(stage3_carries[0][12]));

// bits 16-18 come directly from prev stage
assign stage3_level1_sums[18:16] = stage2_sums[1][13:11];


// stage3 level2

// bits 0, 1 come straight from stage2
assign stage3_level2_sums[1:0] = stage2_carries[1][1:0];

// half adder for bit 2
ha ha_s3_l2_b2 (.a(stage2_carries[1][2]), .b(a[9] & b[0]), .s(stage3_level2_sums[2]), .cout(stage3_carries[1][0]));

// bits 3 to 12 full adders
generate
    for(o=3; o <= 12; o++)
    begin
        fa fa_s3_l2 (.a(stage2_carries[1][o]), .b(a[9] & b[o-2]), .cin(a[10] & b[o-3]), .s(stage3_level2_sums[o]), .cout(stage3_carries[1][o-2]));
    end
endgenerate

// bit 13 comes straight from above
assign stage3_level2_sums[13] = a[10] & b[10];

// stage4
logic [20:0] stage4_level1_sums;
logic [14:0] stage4_level1_carries;

// level2 at this point is a single line. ignore for this stage.

// bits 3:0 come from previous stage
assign stage4_level1_sums[3:0] = stage3_level1_sums[3:0];

// half adders for bits 4 to 6
ha ha_s4_l1_b4 (.a(stage3_level1_sums[4]), .b(stage3_carries[0][0]), .s(stage4_level1_sums[4]), .cout(stage4_level1_carries[0]));
ha ha_s4_l1_b5 (.a(stage3_level1_sums[5]), .b(stage3_carries[0][1]), .s(stage4_level1_sums[5]), .cout(stage4_level1_carries[1]));
ha ha_s4_l1_b6 (.a(stage3_level1_sums[6]), .b(stage3_carries[0][2]), .s(stage4_level1_sums[6]), .cout(stage4_level1_carries[2]));

// full adders for bits 7 to 16
generate
    for(p=7; p <=16; p++)
    begin
        fa fa_s4_l1 (.a(stage3_level1_sums[p]), .b(stage3_carries[0][p-4]), .cin(stage3_level2_sums[p-7]), .s(stage4_level1_sums[p]), .cout(stage4_level1_carries[p-4]));
    end
endgenerate

// half adders for bits 17, 18
ha ha_s4_l1_b17 (.a(stage3_level1_sums[17]), .b(stage3_level2_sums[10]), .s(stage4_level1_sums[17]), .cout(stage4_level1_carries[13]));
ha ha_s4_l1_b18 (.a(stage3_level1_sums[18]), .b(stage3_level2_sums[11]), .s(stage4_level1_sums[18]), .cout(stage4_level1_carries[14]));

// bits 19, 20 come straight from stage3
assign stage4_level1_sums[20:19] = stage3_level2_sums[13:12];



// stage5
logic [20:0] stage5_sums;
logic [15:0] stage5_carries;

// bits 0 to 4
assign stage5_sums[4:0] = stage4_level1_sums[4:0];

// bits 5 to 9
ha ha_s5_b5 (.a(stage4_level1_sums[5]), .b(stage4_level1_carries[0]), .s(stage5_sums[5]), .cout(stage5_carries[0]));
ha ha_s5_b6 (.a(stage4_level1_sums[6]), .b(stage4_level1_carries[1]), .s(stage5_sums[6]), .cout(stage5_carries[1]));
ha ha_s5_b7 (.a(stage4_level1_sums[7]), .b(stage4_level1_carries[2]), .s(stage5_sums[7]), .cout(stage5_carries[2]));
ha ha_s5_b8 (.a(stage4_level1_sums[8]), .b(stage4_level1_carries[3]), .s(stage5_sums[8]), .cout(stage5_carries[3]));
ha ha_s5_b9 (.a(stage4_level1_sums[9]), .b(stage4_level1_carries[4]), .s(stage5_sums[9]), .cout(stage5_carries[4]));

// bits 10 to 19
generate
    for(q = 10; q <= 19; q++)
    begin
        fa fa_s5 (.a(stage4_level1_sums[q]), .b(stage4_level1_carries[q-5]), .cin(stage3_carries[1][q-10]), .s(stage5_sums[q]), .cout(stage5_carries[q-5]));
    end
endgenerate

// bit 20
ha ha_s5_b20 (.a(stage4_level1_sums[20]), .b(stage3_carries[1][10]), .s(stage5_sums[20]), .cout(stage5_carries[15]));

logic [22:0] product;

assign product = ({1'b0, stage5_sums} + {stage5_carries, 6'b0});

assign overflow = product[21];
assign result = product[20:8];      // Multiply result is the num_bits output bits plus two more: the R and S bits for rounding.
assign round_loss = |product[7:0];

endmodule
