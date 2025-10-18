`include "xbar_params.svh"
`include "xbar_if.sv"

module naive_xbar #(
    parameter int SIZE = `XBAR_SIZE,
    parameter int DWIDTH = `XBAR_WIDTH
) (xbar_if.xbar xif);

    genvar i;
    generate
      for (i = 0; i < SIZE; i++) begin : gen_route
        assign xif.dout[i] = en ? xif.din[xif.shift[i]] : '0;
      end
    endgenerate

endmodule
