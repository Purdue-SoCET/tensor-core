`timescale 1ns / 10ps

module flex_counter_tb();

// Parameters
localparam CLK_PERIOD = 1;

// Testbench Signals
logic tb_clk;
logic tb_nrst;
logic tb_enable;
logic [0:15] tb_count;

always
begin
    tb_clk = 1'b0;
    #(CLK_PERIOD/2.0);
    tb_clk = 1'b1;
    #(CLK_PERIOD/2.0);
end

flex_counter DUT (.nrst(tb_nrst), .clk(tb_clk), .enable(tb_enable), .count(tb_count));

initial begin

    tb_nrst = 1'b1;
    tb_enable = 1'b0;
    #(CLK_PERIOD*2);

    // Power on Reset
    tb_nrst = 1'b0;
    #(CLK_PERIOD*2);
    tb_nrst = 1'b1;
    #(CLK_PERIOD*2);

    // Count
    tb_enable = 1'b1;
    #(CLK_PERIOD*32);

    tb_enable = 1'b0;
    #(CLK_PERIOD*32);

    $stop;
end

endmodule