/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef XBAR_PKG_SV
`define XBAR_PKG_SV

package xbar_pkg;
    `include "xbar_params.svh"

    // typedef enum logic [7:0] { BE_COMBINATIONAL = 8'b00000000, BE_FULLY_PIPELINED = 8'b11111111, BE_INTO_5 = 8'b01011010, BE_INTO_3 = 8'b00011000 } benes_mask_t;

    typedef enum logic [13:0] { BA_COMBINATIONAL = 14'b00000000000000, BA_FULLY_PIPELINED = 14'b11111111111111, BA_INTO_5 = 14'b00100100100100, BA_INTO_3 = 14'b00001000010000 } batcher_mask_t;

endpackage

`endif