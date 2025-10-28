module cbg_benes_tb;
    localparam int SIZE=32;
    localparam int DWIDTH=16;
    localparam int TAGWIDTH=$clog2(SIZE);
    localparam int STAGES = (2 * TAGWIDTH) - 1;
    localparam int BITWIDTH = STAGES * (SIZE >> 1);

    logic clk, n_rst;
    logic [BITWIDTH-1:0] control_bit ;
    
endmodule