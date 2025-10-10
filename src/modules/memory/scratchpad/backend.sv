`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module backend #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    input logic clk, n_rst,
    scpad_if.backend_sched bshif,
    scpad_if.backend_scpads bscif,
    scpad_if.backend_dram bdrif
); 
    import scpad_types_pkg::*;

endmodule