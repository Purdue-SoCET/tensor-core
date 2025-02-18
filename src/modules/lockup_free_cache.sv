`include "cache_types_pkg.svh";

module lockup_free_cache (
    input logic CLK, nRST,
    input logic mem_in,
    input logic [3:0] mem_in_uuid,
    input logic [31:0] mem_in_addr,
    input logic mem_in_rw_mode, // 0 = read, 1 = write
    input logic [31:0] mem_in_store_value,
    output logic stall,
    output logic hit,
    output logic [NUM_BANKS-1:0] block_status,
    output logic [NUM_BANKS-1:0][3:0] uuid_block
);

endmodule