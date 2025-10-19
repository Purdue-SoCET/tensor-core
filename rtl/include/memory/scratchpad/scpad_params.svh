/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef SCPAD_PARAMS_SVH
`define SCPAD_PARAMS_SVH

    parameter int unsigned SCPAD_SIZE_BYTES = 1*1024*1024;
    parameter int unsigned NUM_COLS = 32;
    parameter int unsigned ELEM_BITS = 16;
    parameter int unsigned SRAM_VERT_FOLD_FACTOR = 2; // how many elements to pack horizontally to make AR ~~ 1; (ensure height !>>> width)
    parameter int unsigned MAX_SRAM_DELAY = 3;
    parameter int unsigned DRAM_ADDR_WIDTH  = 32;
    parameter string XBAR_TYPE = "NAIVE";
    parameter int unsigned NUM_SCPADS   = 2;
    parameter int unsigned DRAM_ID_WIDTH  = 8; // upper 5 is for 32 rows, bottom 3 is for offset within rows
    parameter int LATCH_INT = 0; // 1, to ignore latches in the hot path. 

`endif
