// 11 bit pipelined wallace tree multiplier.
// by: Mixuan Pan and Vinay Pundith, Spring 2025

`timescale 1ns/1ps

module mul_wallacetree #(parameter num_bits = 11) (input logic clk, nRST, start, stop, input logic [num_bits-1:0] op1, op2, output logic [num_bits-1:0] result, output logic overflow, round_loss);

logic [3:0][num_bits+2:0] stage1_sums;
logic [3:0][num_bits:0] stage1_carries;




genvar i, j, k, l;


generate                                // stage1 levels 1 through 3
    for(i = 0; i < 3; i++)
    begin
        stage1_sums[i][0] = a[i*3] & b[0];       // LSB of level's sums array is a0b0 for level1, a3b0 for l2, a6b0 for l3, etc
        stage1_sums[i][-1] = a[i*3 +2] & b[num_bits-1];
        
        ha ha_00_first (.a(a[i*3] & b[1]), .b(a[i*3 + 1] & b[0]), .s(stage1_sums[i][1]), .cout(stage1_carries[i][0]));
        ha ha_00_last (.a(a[i*3 + 1] & b[num_bits-1]), .b(a[i*3 + 2] & b[num_bits-2]), .s(stage1_sums[i][num_bits]), .cout(state1_carries[i][num_bits]));
        
        generate
            for (j = 0; j < 9, j++)
            begin
                fa fa_00 .a(a[i*3] & b[j+2], .b(a[i*3 +1] & b[j+1]), .cin(a[i*3 + 2] & b[j]), .sum(stage1_sums[i][j+2]), .cout(stage1_carries[i][j+1]));
            end
        endgenerate
    end
endgenerate

// Hard coded stage1 level4
stage1_sums[3][0] = a[9] & b[0];
generate
    for(j=1, j <=10; j++)
    begin
        ha ha_s1_l4 (.a(a[10] & b[j]), .b(a[10] & b[j-1]), .s(stage1_sums[j]), .cout(stage1_carries[j-1]));
    end
endgenerate

logic [2:0][12:0] stage2_carries;
logic [2:0][15:0] stage2_sums;

// stage2 level1
stage2_sums[0][1:0] = stage1_sums[0][1:0];
ha ha_s2_l1_b2 (.a(stage1_sums[0][2]), .b(stage1_carries[0][0]), .s(stage2_sums[0][2]), .cout(stage2_carries[0]));
generate
    for(k=3; k<=12; k++)
    begin
        fa fa_s2_l1 (.a(stage1_sums[0][k]), .b(stage1_carries[0][k-2]), .cin(stage1_sums[1][k-3]), .s(stage2_sums[0][k]), .cout(stage2_carries[0][k-2]));
    end
endgenerate
stage2_sums[0][15:13] = stage1_sums[1][12:10];

// stage2 level2
stage2_sums[1][0] = stage1_carries[1][0];
ha ha_s2_l2_b1 (.a(stage1_carries[1][1]), .b(stage1_sums[2][0]), .s(stage2_sums[1][1]), .cout[stage2_carries[1][0]]);
ha ha_s2_l2_b2 (.a(stage1_carries[1][2]), .b(stage1_sums[2][1]), .s(stage2_sums[1][2]), .cout[stage2_carries[1][1]]);
generate
    for(l=3; l <= 10; l++)
    begin
        fa fa_s2_l2 (.a(stage1_carries[1][l]), .b(stage1_sums[2][l-1]), .cin(stage1_carries[2][l-3]), .s(stage2_sums[1][l]), .cout(stage2_carries[l-2]));
    end
endgenerate
ha ha_s2_l2_b2 (.a(stage1_sums[2][10]), .b(stage1_carries[2][8]), .s(stage2_sums[1][11]), .cout[stage2_carries[1][10]]);
ha ha_s2_l2_b2 (.a(stage1_sums[2][11]), .b(stage1_carries[2][9]), .s(stage2_sums[1][12]), .cout[stage2_carries[1][11]]);
ha ha_s2_l2_b2 (.a(stage1_sums[2][12]), .b(stage1_carries[2][10]), .s(stage2_sums[1][13]), .cout[stage2_carries[1][12]]);


// stage2 level3
stage2_sums[2][1:0] = stage1_sums[3][1:0];
generate
    for(m=2; m <= 11; m++)
    begin
        ha ha_s2_l3 (.a(stage1_sums[3][m]), .b(stage1_carries[3][m-2]), .s(stage2_sums[2][m]), .cout(stage2_carries[2][m-2]));
    end
endgenerate


// stage 2: 
endmodule
