`ifndef CACHE_TYPES_PKG_VH
`define CACHE_TYPES_PKG_VH


parameter CACHE_SIZE = 1024;
parameter BLOCK_SIZE = 4;
parameter NUM_WAYS = 4;
parameter NUM_BANKS = 4;
parameter MSHR_BUFFER_LEN = 8;

localparam NUM_SETS = (CACHE_SIZE / 4) / (BLOCK_SIZE * NUM_WAYS);
localparam NUM_SETS_PER_BANK = NUM_SETS / NUM_BANKS;
localparam BYTE_OFF_BIT_LEN = 2;
localparam BLOCK_OFF_BIT_LEN = $clog2(BLOCK_SIZE);
localparam BLOCK_INDEX_BIT_LEN = $clog2(NUM_SETS);
localparam TAG_BIT_LEN = 32 - BLOCK_INDEX_BIT_LEN - BLOCK_OFF_BIT_LEN - BYTE_OFF_BIT_LEN;

typedef struct packed {
    logic [TAG_BIT_LEN-1:0] tag;
    logic [BLOCK_INDEX_BIT_LEN-1:0] index;
    logic [BLOCK_OFF_BIT_LEN-1:0] block_offset;
    logic [BYTE_OFF_BIT_LEN-1:0] byte_offset;
} addr_t;

typedef struct packed {
    logic [3:0] uuid;
    addr_t addr;
    logic rw_mode; // 0 = read, 1 = write
    logic [31:0] store_value;
} in_mem_instr;

typedef struct packed {
    logic valid;
    logic [3:0] uuid;
    addr_t block_addr;
    logic [BLOCK_SIZE-1:0] write_status;
    logic [BLOCK_SIZE-1:0][31:0] write_block;
} mshr_reg;

typedef struct packed {
    logic valid;
    logic dirty;
    logic [TAG_BIT_LEN-1:0] tag;
    logic [BLOCK_SIZE-1:0][31:0] block;
} cache_frame;

typedef cache_frame [NUM_WAYS-1:0] cache_set;

`endif