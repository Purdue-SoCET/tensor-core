module lockup_free_cache #(
    parameter CACHE_SIZE = 1024,
    parameter BLOCK_SIZE = 4,
    parameter NUM_WAYS = 4,
    parameter NUM_BANKS = 4
) (
    input logic [3:0] mem_in_uuid,
    input logic [31:0] mem_in_addr,
    input logic mem_in_rw_mode,
    input logic [31:0] mem_in_store_value,
    output logic stall,
    output logic hit,
    output logic [NUM_BANKS-1:0] block_status,
    output logic [NUM_BANKS-1:0][3:0] uuid_block
);

endmodule