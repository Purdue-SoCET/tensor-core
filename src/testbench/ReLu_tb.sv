`timescale 1ns / 10ps

module ReLu_tb();

// Parameters
localparam CLK_PERIOD = 10;

// Testbench Signals
logic [15:0]tb_mac_out, tb_relu_out; //16 bits
logic tb_relu_enable;

ReLu #(.BITS(16)) DUT (.relu_enable(tb_relu_enable), .mac_out(tb_mac_out), .relu_out(tb_relu_out));

initial begin
    $dumpfile("ReLu Waveform.fst");
    $dumpvars(0, ReLu_tb);

    tb_relu_enable = 0;
    tb_mac_out = '0;

    //Case 1 : MAC output is positive
    tb_relu_enable = 1;
    tb_mac_out = 16'h0101;
    #(CLK_PERIOD);
    if (tb_relu_out != 16'h0101) begin
        $display("MAC output is positive. ReLu output should be 16'h0101");
    end

    //Case 2 : MAC output is negative
    tb_mac_out = 16'hffff;
    #(CLK_PERIOD);
    if (tb_relu_out != '0) begin
        $display("MAC output is negative. ReLu output should be 16'h0000");
    end

    //Case 3 : MAC output is zero
    tb_mac_out = '0;
    #(CLK_PERIOD);
    if (tb_relu_out != '0) begin
        $display("MAC output is zero. ReLu output should be 16'h0000");
    end

    $finish;
end
endmodule