`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module benes_xbar #(
    parameter int SIZE = 8
    parameter int DWIDTH = 16
) (
    input  logic clk, n_rst,
    input logic en, 
    input logic [DWIDTH-1:0] din [SIZE], 
    input logic [$clog2(SIZE)-1:0] shift [SIZE], 
    output logic [DWIDTH-1:0] dout [SIZE]
);
    import scpad_types_pkg::*;

endmodule