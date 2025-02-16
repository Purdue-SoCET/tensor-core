module lockup_free_cache #(
    parameter CACHE_SIZE = 1024,
    parameter BLOCK_SIZE = 4,
    parameter NUM_WAYS = 4,
    parameter NUM_BANKS = 4,
    parameter MSHR_BUFFER_LEN = 8
) (
    input logic CLK, nRST,
    input logic [3:0] mem_in_uuid,
    input logic [31:0] mem_in_addr,
    input logic mem_in_rw_mode, // 0 = read, 1 = write
    input logic [31:0] mem_in_store_value,
    output logic stall,
    output logic hit,
    output logic [NUM_BANKS-1:0] block_status,
    output logic [NUM_BANKS-1:0][3:0] uuid_block
);
    localparam NUM_SETS = (CACHE_SIZE / 4) / (BLOCK_SIZE * NUM_WAYS);
    localparam NUM_SETS_PER_BANK = NUM_SETS / NUM_BANKS;
    localparam BYTE_OFF_BIT_LEN = 2;
    localparam BLOCK_OFF_BIT_LEN = $clog2(BLOCK_SIZE);
    localparam BLOCK_INDEX_BIT_LEN = $clog2(NUM_SETS);
    localparam TAG_BIT_LEN = 32 - BLOCK_INDEX_BIT_LEN - BLOCK_OFF_BIT_LEN - BYTE_OFF_BIT_LEN;
    `include "cache_types_pkg.svh";

endmodule