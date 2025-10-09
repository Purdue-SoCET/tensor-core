module benes_network (
    input logic CLK, nRST,
    input logic [15:0] in [31:0],
    input logic [143:0] control_bit,
    output logic [15:0] out [31:0] 
);

    logic [15:0] out_1 [31:0];

    logic [15:0] in_2 [31:0];
    logic [15:0] out_2 [31:0];

    logic [15:0] in_3 [31:0];
    logic [15:0] out_3 [31:0];

    logic [15:0] in_4 [31:0];
    logic [15:0] out_4 [31:0];

    logic [15:0] in_5 [31:0];
    logic [15:0] out_5 [31:0];

    logic [15:0] in_6 [31:0];
    logic [15:0] out_6 [31:0];

    logic [15:0] in_7 [31:0];
    logic [15:0] out_7 [31:0];

    logic [15:0] in_8 [31:0];
    logic [15:0] out_8 [31:0];

    logic [15:0] in_9 [31:0];

    genvar i;

    generate
        
        // stage 1
        for(i = 0; i < 32; i = i + 2) begin : stage_1
            localparam int ctrl = i / 2;
            assign out_1[i] = (~control_bit[ctrl]) ? in[i] : in[i + 1];
            assign out_1[i + 1] = (~control_bit[ctrl]) ? in[i + 1] : in[i];
        end

        // stage 2
        for(i = 0; i < 2; i = i + 1) begin : stage_2_1
            localparam int ctrl = (i) + 16;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 4; i < 6; i = i + 1) begin : stage_2_2
            localparam int ctrl = (i) + 16 - 2;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 8; i < 10; i = i + 1) begin : stage_2_3
            localparam int ctrl = (i) + 16 - 4;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 12; i < 14; i = i + 1) begin : stage_2_4
            localparam int ctrl = (i) + 16 - 6;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 16; i < 18; i = i + 1) begin : stage_2_5
            localparam int ctrl = (i) + 16 - 8;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 20; i < 22; i = i + 1) begin : stage_2_6
            localparam int ctrl = (i) + 16 - 10;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 24; i < 26; i = i + 1) begin : stage_2_7
            localparam int ctrl = (i) + 16 - 12;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end
        for(i = 28; i < 30; i = i + 1) begin : stage_2_8
            localparam int ctrl = (i) + 16 - 14;
            assign out_2[i] = (~control_bit[ctrl]) ? in_2[i] : in_2[i + 2];
            assign out_2[i + 2] = (~control_bit[ctrl]) ? in_2[i + 2] : in_2[i];
        end

        // stage 3
        for(i = 0; i < 4; i = i + 1) begin : stage_3_1
            localparam int ctrl = (i) + 32;
            assign out_3[i] = (~control_bit[ctrl]) ? in_3[i] : in_3[i + 4];
            assign out_3[i + 4] = (~control_bit[ctrl]) ? in_3[i + 4] : in_3[i];
        end
        for(i = 8; i < 12; i = i + 1) begin : stage_3_2
            localparam int ctrl = (i) + 32 - 4;
            assign out_3[i] = (~control_bit[ctrl]) ? in_3[i] : in_3[i + 4];
            assign out_3[i + 4] = (~control_bit[ctrl]) ? in_3[i + 4] : in_3[i];
        end
        for(i = 16; i < 20; i = i + 1) begin : stage_3_3
            localparam int ctrl = (i) + 32 - 8;
            assign out_3[i] = (~control_bit[ctrl]) ? in_3[i] : in_3[i + 4];
            assign out_3[i + 4] = (~control_bit[ctrl]) ? in_3[i + 4] : in_3[i];
        end
        for(i = 24; i < 28; i = i + 1) begin : stage_3_4
            localparam int ctrl = (i) + 32 - 12;
            assign out_3[i] = (~control_bit[ctrl]) ? in_3[i] : in_3[i + 4];
            assign out_3[i + 4] = (~control_bit[ctrl]) ? in_3[i + 4] : in_3[i];
        end

        // stage 4
        for(i = 0; i < 8; i = i + 1) begin : stage_4_1
            localparam int ctrl = (i) + 48;
            assign out_4[i] = (~control_bit[ctrl]) ? in_4[i] : in_4[i + 8];
            assign out_4[i + 8] = (~control_bit[ctrl]) ? in_4[i + 8] : in_4[i];
        end
        for(i = 16; i < 24; i = i + 1) begin : stage_4_2
            localparam int ctrl = (i) + 48 - 8;
            assign out_4[i] = (~control_bit[ctrl]) ? in_4[i] : in_4[i + 8];
            assign out_4[i + 8] = (~control_bit[ctrl]) ? in_4[i + 8] : in_4[i];
        end

        // stage 5
        for(i = 0; i < 16; i = i + 1) begin : stage_5
            localparam int ctrl = (i) + 64;
            assign out_5[i] = (~control_bit[ctrl]) ? in_5[i] : in_5[i + 16];
            assign out_5[i + 16] = (~control_bit[ctrl]) ? in_5[i + 16] : in_5[i];
        end

        // stage 6
        for(i = 0; i < 8; i = i + 1) begin : stage_6_1
            localparam int ctrl = (i) + 80;
            assign out_6[i] = (~control_bit[ctrl]) ? in_6[i] : in_6[i + 8];
            assign out_6[i + 8] = (~control_bit[ctrl]) ? in_6[i + 8] : in_6[i];
        end
        for(i = 16; i < 24; i = i + 1) begin : stage_6_2
            localparam int ctrl = (i) + 80 - 8;
            assign out_6[i] = (~control_bit[ctrl]) ? in_6[i] : in_6[i + 8];
            assign out_6[i + 8] = (~control_bit[ctrl]) ? in_6[i + 8] : in_6[i];
        end

        // stage 7
        for(i = 0; i < 4; i = i + 1) begin : stage_7_1
            localparam int ctrl = (i) + 96;
            assign out_7[i] = (~control_bit[ctrl]) ? in_7[i] : in_7[i + 4];
            assign out_7[i + 4] = (~control_bit[ctrl]) ? in_7[i + 4] : in_7[i];
        end
        for(i = 8; i < 12; i = i + 1) begin : stage_7_2
            localparam int ctrl = (i) + 96 - 4;
            assign out_7[i] = (~control_bit[ctrl]) ? in_7[i] : in_7[i + 4];
            assign out_7[i + 4] = (~control_bit[ctrl]) ? in_7[i + 4] : in_7[i];
        end
        for(i = 16; i < 20; i = i + 1) begin : stage_7_3
            localparam int ctrl = (i) + 96 - 8;
            assign out_7[i] = (~control_bit[ctrl]) ? in_7[i] : in_7[i + 4];
            assign out_7[i + 4] = (~control_bit[ctrl]) ? in_7[i + 4] : in_7[i];
        end
        for(i = 24; i < 28; i = i + 1) begin : stage_7_4
            localparam int ctrl = (i) + 96 - 12;
            assign out_7[i] = (~control_bit[ctrl]) ? in_7[i] : in_7[i + 4];
            assign out_7[i + 4] = (~control_bit[ctrl]) ? in_7[i + 4] : in_7[i];
        end

        // stage 8
        for(i = 0; i < 2; i = i + 1) begin : stage_8_1
            localparam int ctrl = (i) + 112;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 4; i < 6; i = i + 1) begin : stage_8_2
            localparam int ctrl = (i) + 112 - 2;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 8; i < 10; i = i + 1) begin : stage_8_3
            localparam int ctrl = (i) + 112 - 4;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 12; i < 14; i = i + 1) begin : stage_8_4
            localparam int ctrl = (i) + 112 - 6;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 16; i < 18; i = i + 1) begin : stage_8_5
            localparam int ctrl = (i) + 112 - 8;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 20; i < 22; i = i + 1) begin : stage_8_6
            localparam int ctrl = (i) + 112 - 10;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 24; i < 26; i = i + 1) begin : stage_8_7
            localparam int ctrl = (i) + 112 - 12;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end
        for(i = 28; i < 30; i = i + 1) begin : stage_8_8
            localparam int ctrl = (i) + 112 - 14;
            assign out_8[i] = (~control_bit[ctrl]) ? in_8[i] : in_8[i + 2];
            assign out_8[i + 2] = (~control_bit[ctrl]) ? in_8[i + 2] : in_8[i];
        end

        // stage 9
        for(i = 0; i < 32; i = i + 2) begin : stage_9
            localparam int ctrl = (i / 2) + 128;
            assign out[i] = (~control_bit[ctrl]) ? in_9[i] : in_9[i + 1];
            assign out[i + 1] = (~control_bit[ctrl]) ? in_9[i + 1] : in_9[i];
        end
    endgenerate


    always_ff @( posedge CLK or negedge nRST) begin : blockName
        if(~nRST) begin
            in_2 <= '{default: 16'b0};
            in_3 <= '{default: 16'b0};
            in_4 <= '{default: 16'b0};
            in_5 <= '{default: 16'b0};
            in_6 <= '{default: 16'b0};
            in_7 <= '{default: 16'b0};
            in_8 <= '{default: 16'b0};
            in_9 <= '{default: 16'b0};
        end
        else begin
            in_2 <= out_1;
            in_3 <= out_2;
            in_4 <= out_3;
            in_5 <= out_4;
            in_6 <= out_5;
            in_7 <= out_6;
            in_8 <= out_7;
            in_9 <= out_8;
        end
    end
endmodule