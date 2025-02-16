`ifndef CACHE_TYPES_PKG_VH
`define CACHE_TYPES_PKG_VH

typedef struct packed {
    logic [TAG_BIT_LEN-1:0] tag;
    logic [BLOCK_INDEX_BIT_LEN-1:0] index;
    logic [BLOCK_OFF_BIT_LEN-1:0] block_offset;
    logic [BYTE_OFF_BIT_LEN-1:0] byte_offset;
} addr_t;

typedef struct packed {
    logic [3:0] uuid;
    addr_t addr;
    logic rw_mode;
    logic [31:0] store_valu;
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