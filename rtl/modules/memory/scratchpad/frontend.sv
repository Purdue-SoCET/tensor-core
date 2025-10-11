`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module frontend #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.frontend_vec fvif, 
    scpad_if.frontend_body fsif
); 
    import scpad_types_pkg::*;


endmodule