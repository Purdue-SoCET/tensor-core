`ifndef XBAR_IF_SV
`define XBAR_IF_SV

interface xbar_if #(
    parameter int SIZE = 8,
    parameter int DWIDTH = 16
) (input logic clk, input logic n_rst);

    `include "xbar_params.svh"

    typedef struct packed {
        logic [DWIDTH-1:0] din;
        logic [$clog2(SIZE)-1:0] shift;
    } group_t;

    logic en;
    group_t in [SIZE]; 
    logic [DWIDTH-1:0] out [SIZE]; 
    
    modport xbar (
        input clk, n_rst,
        input en, in, 
        output out
    );

    modport xbar_tb (
        output clk, n_rst,
        output en, in, 
        input out
    );

endinterface

`endif 
