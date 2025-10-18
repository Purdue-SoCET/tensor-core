`timescale 1ps/1ps

`include "xbar_if.sv"

module naive_xbar_tb;
    import utils

    localparam CLK_PERIOD = 10; 
    
    logic clk, n_rst;

    always #(CLK_PERIOD/2) clk = ~clk;

    xbar_if xif(clk, n_rst);
    
    naive_xbar DUT (xif);

    initial begin
        n_rst = 0;
        repeat (5) @(posedge clk);
        n_rst = 1;
    end

    string fname, wavepath; 
    getenv("WAVEPATH", wavepath);
    $sformat(fname, "%s/head_tb.vcd", wavepath); 

    // initial begin 
    //     $dumpfile(fname);
    //     $dumpvars(0);
    // end 

    test PROG (.xif(xif)); 

    initial begin
        #(10_000 * CLK_PERIOD) $fatal(1, "[TB] Timeout");
    end

endmodule
