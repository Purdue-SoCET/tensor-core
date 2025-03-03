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
    output logic [31:0] hit_load,
    output logic [NUM_BANKS-1:0] block_status,
    output logic [NUM_BANKS-1:0][3:0] uuid_block,

    // RAM Signals
    output logic ram_mem_REN,
    output logic ram_mem_WEN,
    output logic [31:0] ram_mem_addr,
    output logic [31:0] ram_mem_store,
    input logic [31:0] ram_mem_data,
    input logic ram_mem_complete
);

    in_mem_instr hit_check_instr;
    logic [NUM_BANKS-1:0] hit_check;

    assign hit_check_instr.uuid = mem_in_uuid;
    assign hit_check_instr.addr = addr_t'(mem_in_addr);
    assign hit_check_instr.rw_mode = mem_in_rw_mode;
    assign hit_check_instr.store_value = mem_in_store_value;
 

    logic [NUM_BANKS-1:0] miss;
    in_mem_instr new_miss;
    logic [NUM_BANKS-1:0] bank_hit;
    logic [NUM_BANKS-1:0] bank_stall;
    logic [NUM_BANKS-1:0] bank_busy;
    logic [NUM_BANKS-1:0] hit_return_load;

    mshr_reg [NUM_BANKS-1:0] mshr_out;

    logic [BANKS_LEN-1:0] bank_id;
    assign bank_id = mem_in_addr & (NUM_BANKS - 1);
    
    assign new_miss.uuid = mem_in_uuid;
    assign new_miss.addr = addr_t'(mem_in_addr);
    assign new_miss.rw_mode = mem_in_rw_mode;
    assign new_miss.store_value = mem_in_store_value;

    genvar i;
    generate
        for (i = 0; i < NUM_BANKS; i++) begin : BANK_GEN
            cache_mshr_buffer mshr_buffer_i (
                .CLK           (CLK),
                .nRST          (nRST),
                .miss          (miss[i]),
                .mem_instr     (new_miss),
                .bank_empty    (~bank_busy[i]),
                .mshr_out      (mshr_out[i]),
                .stall         (bank_stall[i])
            );
            cache_bank u_cache_bank (
                .CLK                   (CLK),
                .nRST                  (nRST),
                .bank_id               (bank_id),
                // for requesting RAM
                .instr_valid           (hit_check[i]),
                // valid single-cycle request 
                .ram_mem_data          (ram_mem_data),
                // data incoming from RAM
                .mshr_entry            (mshr_out[i]),
                .mem_instr_in          (hit_check_instr),
                .ram_mem_complete      (ram_mem_complete),
                // RAM completed operation
                .cache_bank_busy       (bank_busy[i]),
                // High when MSHR in-flight
                .scheduler_hit         (bank_hit[i]),
                .ram_mem_REN           (ram_mem_REN),
                .ram_mem_WEN           (ram_mem_WEN),
                .ram_mem_store         (ram_mem_store),
                .ram_mem_addr          (ram_mem_addr),
                .scheduler_data_out    (hit_return_load[i]),
                .scheduler_uuid_out    (uuid_block[i]),
                .scheduler_uuid_ready  (block_status[i])
            );
        end
    endgenerate

    always_comb begin
        miss = 0;
        stall = 0;
        hit = 0;
        block_status = 0;
        uuid_block = 0;
        hit_load = 0;

        if (bank_hit == 0) begin
            miss[bank_id] = 1;
        end
        if (bank_stall != 0) begin
            stall = 1;
        end
        for (int j = 0; j < NUM_BANKS; j++) begin
            if (bank_hit[j]) begin
                hit = 1;
                hit_load = hit_return_load[j];
            end
        end
    end

endmodule