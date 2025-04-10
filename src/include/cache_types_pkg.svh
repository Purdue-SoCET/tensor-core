`ifndef CACHE_TYPES_PKG_VH
`define CACHE_TYPES_PKG_VH

    parameter CACHE_SIZE = 1024;
    parameter BLOCK_SIZE = 4;
    parameter WORD_SIZE = 1; 
    parameter NUM_WAYS = 4;
    parameter NUM_BANKS = 4;
    parameter MSHR_BUFFER_LEN = 8;
    parameter CACHE_RW_SIZE = 32; 
    parameter UUID_SIZE = 4; 

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

    typedef enum logic [3:0] { 
        START, BLOCK_PULL, VICTIM_EJECT, FINISH, FLUSH, WRITEBACK, HALT
    } bank_fsm_states; 

    typedef cache_frame [NUM_WAYS-1:0] cache_set;

`endif

