`timescale 1ns / 1ns

module benes_network_tb;
    parameter PERIOD = 10;

    logic CLK = 1;
    logic nRST;

    always #(PERIOD/2) CLK++;
    
    logic [15:0] in [31:0];
    logic [143:0] control_bit;
    logic [15:0] out [31:0];

    test #(.PERIOD(PERIOD)) PROG (
        .*
    );

    benes_xbar DUT (
        .*
    );

endmodule

program test
(
    input logic CLK, 
    output logic nRST,
    output logic [15:0] in [31:0],
    output logic [143:0] control_bit,
    input logic [15:0] out [31:0] 
);
    parameter PERIOD = 10;
    integer i;
    logic [15:0] val;
initial begin
    nRST = 0;

    #(PERIOD);

    nRST = 1;
    val = 16'd0;

    for (i = 0; i < 32; i = i + 1) begin
        in[i] = val;
        val = val + 16'd1;
    end

    // $display("%d", in[25]);

    // default (output = input)
    // control_bit = 144'b0;

    // perm = [27, 24, 2, 29, 4, 7, 20, 10, 1, 0, 8, 9, 3, 13, 16, 26, 12, 31, 17, 19, 28, 18, 23, 30, 5, 15, 6, 21, 11, 25, 22, 14]
    control_bit = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;  
    
    #(PERIOD);
    #(PERIOD);
    #(PERIOD);
    #(PERIOD);
    #(PERIOD);
    #(PERIOD);
    #(PERIOD);
    #(PERIOD);
    
    for (i = 0; i < 32; i = i + 1) begin
        $display("out %d: %d", i, out[i]);
    end
    $finish;
end
endprogram