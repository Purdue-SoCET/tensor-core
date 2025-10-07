module benes (
    input logic CLK, nRST,
    input logic [31:0] in [15:0],
    input logic [143:0] control_bit,
    output logic [31:0] out [15:0]
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

    genvar i, j;

    generate
        
        // stage 1
        for(i = 0; i < 32; i = i + 2) begin : stage_1
            localparam int curr = i / 2;
            assign out_1[curr] = (~control_bit[curr]) ? in[i] : in[i + 1];
            assign out_1[curr + 16] = (~control_bit[curr]) ? in[i + 1] : in[i];
        end

        // stage 2
        for(i = 0; i < 16; i = i + 2) begin : stage_2_1
            localparam int curr = i / 2;
            assign out_2[curr] = (~control_bit[curr]) ? in_2[i] : in_2[i + 1];
            assign out_2[curr + 8] = (~control_bit[curr]) ? in_2[i + 1] : in_2[i];
        end
        for(i = 16; i < 32; i = i + 2) begin : stage_2_2
            localparam int curr = (i / 2) + 8;
            assign out_2[curr] = (~control_bit[curr]) ? in_2[i] : in_2[i + 1];
            assign out_2[curr + 8] = (~control_bit[curr]) ? in_2[i + 1] : in_2[i];
        end

        // stage 3
        for(i = 0; i < 8; i = i + 2) begin : stage_3_1
            localparam int curr = i / 2;
            assign out_3[curr] = (~control_bit[curr]) ? in_3[i] : in_3[i + 1];
            assign out_3[curr + 4] = (~control_bit[curr]) ? in_3[i + 1] : in_3[i];
        end
        for(i = 8; i < 16; i = i + 2) begin : stage_3_2
            localparam int curr = (i / 2) + 4;
            assign out_3[curr] = (~control_bit[curr]) ? in_3[i] : in_3[i + 1];
            assign out_3[curr + 4] = (~control_bit[curr]) ? in_3[i + 1] : in_3[i];
        end
        for(i = 16; i < 24; i = i + 2) begin : stage_3_3
            localparam int curr = (i / 2) + 8;
            assign out_3[curr] = (~control_bit[curr]) ? in_3[i] : in_3[i + 1];
            assign out_3[curr + 4] = (~control_bit[curr]) ? in_3[i + 1] : in_3[i];
        end
        for(i = 24; i < 32; i = i + 2) begin : stage_3_4
            localparam int curr = (i / 2) + 12;
            assign out_3[curr] = (~control_bit[curr]) ? in_3[i] : in_3[i + 1];
            assign out_3[curr + 4] = (~control_bit[curr]) ? in_3[i + 1] : in_3[i];
        end

        // stage 4
        for(i = 0; i < 4; i = i + 2) begin : stage_4_1
            localparam int curr = i / 2;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 4; i < 8; i = i + 2) begin : stage_4_2
            localparam int curr = (i / 2) + 2;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 8; i < 12; i = i + 2) begin : stage_4_3
            localparam int curr = (i / 2) + 4;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 12; i < 16; i = i + 2) begin : stage_4_4
            localparam int curr = (i / 2) + 6;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 16; i < 20; i = i + 2) begin : stage_4_5
            localparam int curr = (i / 2) + 8;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 20; i < 24; i = i + 2) begin : stage_4_6
            localparam int curr = (i / 2) + 10;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 24; i < 28; i = i + 2) begin : stage_4_7
            localparam int curr = (i / 2) + 12;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end
        for(i = 28; i < 32; i = i + 2) begin : stage_4_8
            localparam int curr = (i / 2) + 14;
            assign out_4[curr] = (~control_bit[curr]) ? in_4[i] : in_4[i + 1];
            assign out_4[curr + 2] = (~control_bit[curr]) ? in_4[i + 1] : in_4[i];
        end

        // stage 5
        for(i = 0; i < 4; i = i + 2) begin : stage_5_1
            localparam int curr = i / 2;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 4; i < 8; i = i + 2) begin : stage_5_2
            localparam int curr = (i / 2) + 2;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 8; i < 12; i = i + 2) begin : stage_5_3
            localparam int curr = (i / 2) + 4;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 12; i < 16; i = i + 2) begin : stage_5_4
            localparam int curr = (i / 2) + 6;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 16; i < 20; i = i + 2) begin : stage_5_5
            localparam int curr = (i / 2) + 8;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 20; i < 24; i = i + 2) begin : stage_5_6
            localparam int curr = (i / 2) + 10;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 24; i < 28; i = i + 2) begin : stage_5_7
            localparam int curr = (i / 2) + 12;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end
        for(i = 28; i < 32; i = i + 2) begin : stage_5_8
            localparam int curr = (i / 2) + 14;
            assign out_5[i] = (~control_bit[curr]) ? in_5[curr] : in_5[curr + 1];
            assign out_5[i + 1] = (~control_bit[curr]) ? in_5[curr + 1] : in_5[curr];
        end

        // stage 6
        for(i = 0; i < 8; i = i + 2) begin : stage_6_1
            localparam int curr = (i / 2);
            assign out_6[i] = (~control_bit[curr]) ? in_6[curr] : in_6[curr + 4];
            assign out_6[i + 1] = (~control_bit[curr]) ? in_6[curr + 4] : in_6[curr];
        end
        for(i = 8; i < 16; i = i + 2) begin : stage_6_2
            localparam int curr = (i / 2) + 4;
            assign out_6[i] = (~control_bit[curr]) ? in_6[curr] : in_6[curr + 4];
            assign out_6[i + 1] = (~control_bit[curr]) ? in_6[curr + 4] : in_6[curr];
        end
        for(i = 16; i < 24; i = i + 2) begin : stage_6_3
            localparam int curr = (i / 2) + 8;
            assign out_6[i] = (~control_bit[curr]) ? in_6[curr] : in_6[curr + 4];
            assign out_6[i + 1] = (~control_bit[curr]) ? in_6[curr + 4] : in_6[curr];
        end
        for(i = 24; i < 32; i = i + 2) begin : stage_6_4
            localparam int curr = (i / 2) + 12;
            assign out_6[i] = (~control_bit[curr]) ? in_6[curr] : in_6[curr + 4];
            assign out_6[i + 1] = (~control_bit[curr]) ? in_6[curr + 4] : in_6[curr];
        end

        // stage 7
        for(i = 0; i < 16; i = i + 2) begin : stage_7_1
            localparam int curr = i / 2;
            assign out_7[i] = (~control_bit[curr]) ? in_7[curr] : in_7[curr + 8];
            assign out_7[i + 1] = (~control_bit[curr]) ? in_7[curr + 8] : in_7[curr];
        end
        for(i = 16; i < 32; i = i + 2) begin : stage_7_2
            localparam int curr = (i / 2) + 8;
            assign out_7[i] = (~control_bit[curr]) ? in_7[curr] : in_7[curr + 8];
            assign out_7[i + 1] = (~control_bit[curr]) ? in_7[curr + 8] : in_7[curr];
        end

        // stage 8
        for(i = 0; i < 32; i = i + 2) begin : stage_8
            localparam int curr = i / 2;
            assign out[i] = (~control_bit[curr]) ? in_8[curr] : in_8[curr + 16];
            assign out[i + 1] = (~control_bit[curr]) ? in_8[curr + 16] : in_8[curr];
        end
    endgenerate


    always_ff @( posedge CLK or negedge nRST) begin : blockName
        if(~nRST) begin
            in_2 <= 0;
            in_3 <= 0;
            in_4 <= 0;
            in_5 <= 0;
            in_6 <= 0;
            in_7 <= 0;
            in_8 <= 0;
        end
        else begin
            in_2 <= out_1;
            in_3 <= out_2;
            in_4 <= out_3;
            in_5 <= out_4;
            in_6 <= out_5;
            in_7 <= out_6;
            in_8 <= out_7;
        end
    end
endmodule