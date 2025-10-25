/*  Vinay Jagan - vjagan@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef CACHES_PKG_SV
`define CACHES_PKG_SV

package scpad_pkg;
    `include "caches_params.svh"

    localparam NUM_SETS = (CACHE_SIZE / 4) / (BLOCK_SIZE);
    localparam NUM_SETS_PER_BANK = NUM_SETS / NUM_BANKS;
    localparam NUM_BLOCKS_PER_BANK = NUM_SETS_PER_BANK * NUM_WAYS; 

    localparam BYTE_OFF_BIT_LEN = 2;
    localparam BLOCK_OFF_BIT_LEN = $clog2(BLOCK_SIZE); 
    localparam BLOCK_INDEX_BIT_LEN = $clog2(NUM_SETS); 
    localparam NUM_SETS_PER_BANK_LEN = $clog2(NUM_SETS_PER_BANK); 
    localparam NUM_BLOCKS_LEN = $clog2(BLOCK_SIZE);
    localparam WAYS_LEN = $clog2(NUM_WAYS); 
    localparam BANKS_LEN = $clog2(NUM_BANKS); 
    localparam NUM_BLOCKS_PER_BANK_LEN = $clog2(NUM_BLOCKS_PER_BANK);

    localparam TAG_BIT_LEN = 32 - BLOCK_INDEX_BIT_LEN - BLOCK_OFF_BIT_LEN - BYTE_OFF_BIT_LEN;

    localparam UUID_MAX = (1 << UUID_SIZE) - 1;
    localparam TREE_BITS = NUM_WAYS - 1;              

    localparam MSHR_BUFFER_BIT_LEN = $clog2(MSHR_BUFFER_LEN);

endpackage

`endif

