/*  Vinay Jagan - vjagan@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef SCPAD_PARAMS_SVH
`define SCPAD_PARAMS_SVH

    parameter int unsigned CACHE_SIZE = 1024;
    parameter int unsigned BLOCK_SIZE = 4;
    parameter int unsigned WORD_SIZE = 1; 
    parameter int unsigned NUM_WAYS = 4;
    parameter int unsigned NUM_BANKS = 4;
    parameter int unsigned MSHR_BUFFER_LEN = 8;
    parameter int unsigned CACHE_RW_SIZE = 32; 
    parameter int unsigned UUID_SIZE = 4; 

`endif
