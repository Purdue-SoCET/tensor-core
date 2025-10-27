// 8 bit wallace tree multiplier.
// tell me to parameterize this, and i will throw a snowball at you.
// use for BF16 multiplication.
// version with no pipelining/latches, fully singlecycle.
// by: Mixuan Pan and Vinay Pundith, September 2025

// https://docs.google.com/spreadsheets/d/1gSpQD07Z3azBS7G5FqXazuCA9pSynyPupSXBCeiby4s/edit?gid=1076267634#gid=1076267634

`timescale 1ns/1ps

/* verilator lint_off UNUSEDSIGNAL */
module wallacetree_8b (input logic [7:0] a, b, output logic [9:0] result, output logic overflow, round_loss);//, output logic [15:0] debug_output);



genvar i, j, k, l, n, p;

//------------------------------------------------------------------------------------------------------------------------------------------------------------------
// compression stage1 (level1, level2)
//------------------------------------------------------------------------------------------------------------------------------------------------------------------

logic [1:0][9:0] stage1_sums;
logic [1:0][7:0] stage1_carries;

generate
    for(i = 0; i <=1; i++)
    begin
        assign stage1_sums[i][0] = a[i*3] & b[0];       // LSB of level's sums array is a0b0 for level1, a3b0 for l2, a6b0 for l3, etc
        assign stage1_sums[i][9] = a[i*3 +2] & b[7];
        
        ha ha_00_first (.a(a[i*3] & b[1]), .b(a[i*3 + 1] & b[0]), .s(stage1_sums[i][1]), .cout(stage1_carries[i][0]));
        ha ha_00_last (.a(a[i*3 + 1] & b[7]), .b(a[i*3 + 2] & b[6]), .s(stage1_sums[i][8]), .cout(stage1_carries[i][7]));
        
            for (j = 2; j <=7; j++)
            begin
                fa fa_00 (.a(a[i*3] & b[j]), .b(a[i*3 +1] & b[j-1]), .cin(a[i*3 + 2] & b[j-2]), .s(stage1_sums[i][j]), .cout(stage1_carries[i][j-1]));
            end

    end
endgenerate
//------------------------------------------------------------------------------------------------------------------------------------------------------------------


//------------------------------------------------------------------------------------------------------------------------------------------------------------------
// compression stage2 (level1, level2)
//------------------------------------------------------------------------------------------------------------------------------------------------------------------

logic [12:0] stage2_level1_sums;
logic [9:0] stage2_level2_sums;

logic [1:0][7:0] stage2_carries;

// stage2 level1

// bits 1:0 come straight from stage1
assign stage2_level1_sums[1:0] = stage1_sums[0][1:0];

// half adder for bit 2
ha ha_s2_l1_b2 (.a(stage1_sums[0][2]), .b(stage1_carries[0][0]), .s(stage2_level1_sums[2]), .cout(stage2_carries[0][0]));

// full adders for bits 3 to 9
generate
    for(k=3; k<=9; k++)
    begin
        fa fa_s2_l1 (.a(stage1_sums[0][k]), .b(stage1_carries[0][k-2]), .cin(stage1_sums[1][k-3]), .s(stage2_level1_sums[k]), .cout(stage2_carries[0][k-2]));
    end
endgenerate

//bits 12:10 come straight from stage1
assign stage2_level1_sums[12:10] = stage1_sums[1][9:7];

// stage2 level2

// lowest bit comes straight from stage1 
assign stage2_level2_sums[0] = stage1_carries[1][0];

// half adder for bit 1
ha ha_s2_l2_b1 (.a(stage1_carries[1][1]), .b(a[6] & b[0]), .s(stage2_level2_sums[1]), .cout(stage2_carries[1][0]));

// full adders for bits 2 through 7
generate
    for(l=2; l <= 7; l++)      // Full adders for bits 3 through 10 of result
    begin
        fa fa_s2_l2 (.a(stage1_carries[1][l]), .b(a[6] & b[l-1]), .cin(a[7] & b[l-2]), .s(stage2_level2_sums[l]), .cout(stage2_carries[1][l-1]));
    end
endgenerate

// half adder for bit 8
ha ha_s2_l2_b8 (.a(a[6] & b[7]), .b(a[7] & b[6]), .s(stage2_level2_sums[8]), .cout(stage2_carries[1][7]));

// bit 9
assign stage2_level2_sums[9] = a[7] & b[7];

//------------------------------------------------------------------------------------------------------------------------------------------------------------------



//------------------------------------------------------------------------------------------------------------------------------------------------------------------
// compression stage3  (single 3:2 compression. level2 carries from previous stage are passed directly to stage4)
//------------------------------------------------------------------------------------------------------------------------------------------------------------------
// stage 3:
logic [14:0] stage3_sums;
logic [9:0] stage3_carries;

// level 1
// bits 0 to 2 come directly from prev stage
assign stage3_sums[2:0] = stage2_level1_sums[2:0];

// half adders for bits 3, 4
ha ha_s3_l1_b3 (.a(stage2_level1_sums[3]), .b(stage2_carries[0][0]), .s(stage3_sums[3]), .cout(stage3_carries[0]));
ha ha_s3_l1_b4 (.a(stage2_level1_sums[4]), .b(stage2_carries[0][1]), .s(stage3_sums[4]), .cout(stage3_carries[1]));

// full adders for bits 5 to 10
generate
    for(n = 5; n <=10; n++)
    begin
        fa fa_s3_l1 (.a(stage2_level1_sums[n]), .b(stage2_carries[0][n-3]), .cin(stage2_level2_sums[n-5]), .s(stage3_sums[n]), .cout(stage3_carries[n-3]));
    end
endgenerate

// half adders for bits 11, 12
ha ha_s3_l1_b11 (.a(stage2_level1_sums[11]), .b(stage2_level2_sums[6]), .s(stage3_sums[11]), .cout(stage3_carries[8]));
ha ha_s3_l1_b12 (.a(stage2_level1_sums[12]), .b(stage2_level2_sums[7]), .s(stage3_sums[12]), .cout(stage3_carries[9]));

// bits 14, 13 come directly from prev stage
assign stage3_sums[14:13] = stage2_level2_sums[9:8];

//------------------------------------------------------------------------------------------------------------------------------------------------------------------


//------------------------------------------------------------------------------------------------------------------------------------------------------------------
// compression stage4 (single 3:2 compression)
//------------------------------------------------------------------------------------------------------------------------------------------------------------------
// stage4
logic [14:0] stage4_sums;
logic [10:0] stage4_carries;

// bits 3:0 come from previous stage
assign stage4_sums[3:0] = stage3_sums[3:0];

// half adders for bits 4 to 6
ha ha_s4_l1_b4 (.a(stage3_sums[4]), .b(stage3_carries[0]), .s(stage4_sums[4]), .cout(stage4_carries[0]));
ha ha_s4_l1_b5 (.a(stage3_sums[5]), .b(stage3_carries[1]), .s(stage4_sums[5]), .cout(stage4_carries[1]));
ha ha_s4_l1_b6 (.a(stage3_sums[6]), .b(stage3_carries[2]), .s(stage4_sums[6]), .cout(stage4_carries[2]));

// full adders for bits 7 to 16
generate
    for(p=7; p <=13; p++)
    begin
        fa fa_s4_l1 (.a(stage3_sums[p]), .b(stage3_carries[p-4]), .cin(stage2_carries[1][p-7]), .s(stage4_sums[p]), .cout(stage4_carries[p-4]));
    end
endgenerate

// half adder for bit 14
ha ha_s4_l1_b14 (.a(stage3_sums[14]), .b(stage2_carries[1][7]), .s(stage4_sums[14]), .cout(stage4_carries[10]));

//------------------------------------------------------------------------------------------------------------------------------------------------------------------

logic [16:0] product;

assign product[4:0] = stage4_sums[4:0];


assign product[16:5] = ({1'b0, stage4_sums[14:5]} + stage4_carries);

assign overflow = product[15];
assign result = product[14:5];      // Multiply result is the num_bits output bits plus two more: the R and S bits for rounding.
assign round_loss = |product[4:0];

// assign debug_output = product[15:0];

endmodule
