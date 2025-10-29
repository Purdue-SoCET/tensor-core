`timescale 1ns / 1ns

module benes_xbar_tb;
    parameter PERIOD = 10;
    parameter STAGES = 9;
    parameter SIZE = 32;

    logic [STAGES * (SIZE >> 1)] control_bit;
    logic clk, n_rst;
    initial clk = 1'b0;
    always  #5 clk = ~clk;

    xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));

    test #(.PERIOD(PERIOD)) PROG (
        .*
    );

    benes DUT (
        .*
    );

endmodule

program test #(
    parameter PERIOD = 10,
    parameter STAGES = 9,
    parameter SIZE = 32
) (
    xbar_if.tb xif,
    output logic [STAGES * (SIZE >> 1)] control_bit
);
    integer i;
    logic [15:0] val;
initial begin
    xif.n_rst = 0;

    #(PERIOD);

    xif.n_rst = 1;
    val = 16'd0;

    for (i = 0; i < 32; i = i + 1) begin
        xif.in[i] = val;
        val = val + 16'd1;
    end

    // $display("%d", in[25]);

    // default (output = input)
    // control_bit = 144'b0;
    // automatic int perm [32] = '{27, 24, 2, 29, 4, 7, 20, 10, 1, 0, 8, 9, 3, 13, 16, 26,
    //                 12, 31, 17, 19, 28, 18, 23, 30, 5, 15, 6, 21, 11, 25, 22, 14};
    // int perm [32] = '{27, 24, 2, 29, 4, 7, 20, 10, 1, 0, 8, 9, 3, 13, 16, 26, 12, 31, 17, 19, 28, 18, 23, 30, 5, 15, 6, 21, 11, 25, 22, 14};
    control_bit = 144'b001100100111110100011110011011100000100110000100000000000000000000001100110101001101100000001111000000011100111001110011001001100011101011000111;  
    repeat (10) #(PERIOD);
    
    for (i = 0; i < 32; i = i + 1) begin
        if(xif.out[i] != perm[i]) begin
            $display("wrong input for %d", i);
        end
        // $display("perm %d: %d", i, perm[i]);
        $display("out %d: %d", i, xif.out[i]);
    end
    $finish;
end
endprogram