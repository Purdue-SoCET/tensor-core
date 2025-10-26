/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef XBAR_PKG_SV
`define XBAR_PKG_SV

package xbar_pkg;
    `include "xbar_params.svh"

    // Note. FULLY_PIPELINED and COMBINATIONAL are the base cases for both crossbars. 
    // If you want to do INTO_5 and INTO_3 folding, you'd have to define your own REGISTER_MASK codes and logic for them. 
    // It didn't matter to us to actually parameterize these masks to the SIZE parameter. 
    
    typedef enum logic [7:0] { BE_COMBINATIONAL = 8'b00000000, BE_FULLY_PIPELINED = 8'b11111111, BE_INTO_5 = 8'b01011010, BE_INTO_3 = 8'b00011000 } benes_mask_t;

    typedef enum logic [13:0] { BA_COMBINATIONAL = 14'b00000000000000, BA_FULLY_PIPELINED = 14'b11111111111111, BA_INTO_5 = 14'b00100100100100, BA_INTO_3 = 14'b00001000010000 } batcher_mask_t;

endpackage

`endif