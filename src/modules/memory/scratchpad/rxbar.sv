`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module rxbar #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.xbar_r rif
); 
    import scpad_types_pkg::*;

    generate
        unique case (MODE)
            "NAIVE": xbar u_wxbar_IDX (.a(a), .b(b), .y(y));
        endcase
    endgenerate
endmodule