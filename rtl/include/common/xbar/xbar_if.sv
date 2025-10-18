`ifndef XBAR_IF_SV
`define XBAR_IF_SV

interface xbar_if #(
    parameter int SIZE = 8,
    parameter int DWIDTH = 16
) (input logic clk, input logic n_rst);

    `include "xbar_params.svh"

    logic [DWIDTH-1:0] din [SIZE];
    logic [$clog2(SIZE)-1:0] shift [SIZE]; 
    logic [DWIDTH-1:0] dout [SIZE]; 
    logic en;

    modport xbar (
        input clk, n_rst,
        input en, din, shift, 
        output dout
    );

    modport xbar_tb (
        output clk, n_rst,
        output en, din, shift, 
        input dout
    );

endinterface

`endif 
