`include "xbar_params.svh"
`include "xbar_if.sv"

module batcher_xbar #(
    parameter int SIZE = `XBAR_SIZE
    parameter int DWIDTH = `XBAR_WIDTH
) (xbar_if.xbar xif);
    import xbar_pkg::*;

endmodule