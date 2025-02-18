`timescale 1ps/1ps

module cache_mshr_buffer_tb ();
    localparam CLK_PERIOD = 1;

    logic tb_clk;
    logic pulse;

    always begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2.0);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2.0);
    end

    initial begin
        pulse = 0;
        @(posedge tb_clk);
        @(posedge tb_clk);
        pulse = 1;
        @(posedge tb_clk);
        pulse = 0;
        @(posedge tb_clk);
    end
    
endmodule