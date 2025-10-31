// `include "xbar_params.svh"
// `include "xbar_if.sv"

// module naive_xbar #(
//     parameter int SIZE = 32,
//     parameter int DWIDTH = 16
// ) (xbar_if.xbar xif);

//     genvar i;
//     generate
//       for (i = 0; i < SIZE; i++) begin : gen_route
//         assign xif.out[i] = xif.en ? xif.in.din[xif.in.shift[i]] : '0;
//       end
//     endgenerate

// endmodule
