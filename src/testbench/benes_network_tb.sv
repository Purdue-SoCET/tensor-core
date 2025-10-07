`timescale 1ns / 1ns

module benes_network_tb;
    parameter PERIOD = 10;

    logic CLK = 1;
    logic nRST;

    always #(PERIOD/2) CLK++;
    
    logic [31:0] in [15:0];
    logic [143:0] control_bit;
    logic [31:0] out [15:0];

    test #(.PERIOD(PERIOD)) PROG (
        .*
    );

    benes_network DUT (
        .*
    );

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    output logic [31:0] in [15:0],
    output logic [143:0] control_bit,
    input logic [31:0] out [15:0]
);
initial begin
    parameter PERIOD = 10;
    nRST = 0;

    #(PERIOD);

    nRST = 1;

    in = {16'h0, 16'h1, 16'h2, 16'h3, 16'h4, 16'h5, 16'h6, 16'h7, 16'h8, 16'h9, 16'h10, 16'h11, 16'h12, 16'h13, 16'h14, 16'h15};
    control_bit = 144'b00110011_10101010_00011100_00000011_00000110_10100011_00000000_01011000_01000111_00111000_11001000_11000010_00011001_00011111_11110100_00001101_10110000_00001010;

    // perm = {23, 2, 10, 12, 3, 18, 20, 17, 5, 14, 29, 24, 0, 11, 8, 19, 25, 16, 22, 4, 30, 6, 26, 28, 27, 7, 13, 31, 9, 21, 15, 1};
    
    #(PERIOD);
    $finish;
end
endprogram