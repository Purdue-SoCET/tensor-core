/*  Vinay Jagan - vjagan@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef CACHES_IF_SV
`define CACHES_IF_SV

interface caches_if (input logic clk, input logic n_rst);
    `include "caches_params.svh"

    import caches_pkg::*;

    typedef struct packed {
        logic [TAG_BIT_LEN-1:0] tag;
        logic [BLOCK_INDEX_BIT_LEN-1:0] index;
        logic [BLOCK_OFF_BIT_LEN-1:0] block_offset;
        logic [BYTE_OFF_BIT_LEN-1:0] byte_offset;
    } addr_t;

    typedef struct packed {
        addr_t addr;
        logic rw_mode; // 0 = read, 1 = write
        logic [31:0] store_value;
    } in_mem_instr;

    typedef struct packed {
        logic [WAYS_LEN-1:0] lru_way;
        logic [TREE_BITS-1:0] tree;
    } psuedo_lru_frame;

    typedef logic [BLOCK_SIZE-1:0][31:0] cache_block;

    typedef struct packed {
        logic valid;
        logic [UUID_SIZE-1:0] uuid;
        addr_t block_addr;
        logic [BLOCK_SIZE-1:0] write_status; // WEN==1, REN==0
        cache_block write_block;
    } mshr_reg;

    typedef struct packed {
        logic valid;
        logic dirty;
        logic [TAG_BIT_LEN-1:0] tag;
        cache_block block; // 1 word -> 4 bytes -> 32 bits
    } cache_frame;

    typedef enum logic [4:0] { 
        START, ADDRESS_CALC, LRU_CALC, BUFFER_STATE, BLOCK_PULL, VICTIM_EJECT, FINISH, FLUSH, WRITEBACK, HALT
    } bank_fsm_states; 

    typedef cache_frame [NUM_WAYS-1:0] cache_set;

endinterface

`endif 
