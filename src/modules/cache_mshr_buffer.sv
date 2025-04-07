`include "cache_types_pkg.svh";

module cache_mshr_buffer (
    input logic CLK, nRST,
    input logic miss,
    input logic [BANKS_LEN-1:0] bank_id,
    input in_mem_instr mem_instr,
    input logic bank_empty,
    output mshr_reg mshr_out,
    output logic stall, 
    output logic [UUID_SIZE-1:0] uuid_out
);
    mshr_reg [MSHR_BUFFER_LEN-1:0] buffer, next_buffer;
    mshr_reg [MSHR_BUFFER_LEN-1:0] buffer_copy;
    logic [MSHR_BUFFER_LEN-2:0] secondary_misses;
    mshr_reg mshr_new_miss;
    logic [UUID_SIZE-1:0] uuid, next_uuid;

    assign next_uuid = (uuid == UUID_MAX) ? 8'd0 : (uuid + 1);

    always_comb begin
        mshr_new_miss.valid = miss;
        if ((secondary_misses == 0) && miss) begin
            mshr_new_miss.uuid = next_uuid;
            uuid_out = next_uuid;
        end else begin
            mshr_new_miss.uuid = uuid;
            uuid_out = buffer[0].uuid;
        end
        mshr_new_miss.block_addr = {mem_instr.addr.tag, mem_instr.addr.index, BLOCK_OFF_BIT_LEN'(0), BYTE_OFF_BIT_LEN'(0)};
        mshr_new_miss.write_status = 0;
        mshr_new_miss.write_status[mem_instr.addr.block_offset] = mem_instr.rw_mode;
        mshr_new_miss.write_block = 0;
        mshr_new_miss.write_block[mem_instr.addr.block_offset] = mem_instr.store_value;
    end

    always_ff @( posedge CLK, negedge nRST ) begin
        if (!nRST) begin
            buffer <= 0;
            uuid <= 0;
        end else begin
            buffer <= next_buffer;
            if (miss && (secondary_misses == 0) && (!buffer[0].valid || bank_empty)) uuid <= next_uuid;
        end
    end

    always_comb begin
        buffer_copy = buffer;
        secondary_misses = 0;
        next_buffer = buffer;
        stall = 0;
        mshr_out = buffer[MSHR_BUFFER_LEN - 1];

        for (int i = 0; i < MSHR_BUFFER_LEN - 1; i++) begin
            if (mshr_new_miss.valid && buffer[i].block_addr == mshr_new_miss.block_addr && buffer[i].valid) begin
                buffer_copy[i].write_status = buffer[i].write_status | mshr_new_miss.write_status;
                buffer_copy[i].write_block[mem_instr.addr.block_offset] =  (mem_instr.rw_mode) ? mem_instr.store_value : buffer[i].write_block[mem_instr.addr.block_offset];
                secondary_misses[i] = 1;
            end
        end

        for (int i = 0; i < MSHR_BUFFER_LEN; i++) begin
            if (i == 0) begin
                if (secondary_misses == 0) begin
                    if (!buffer[1].valid || bank_empty) begin
                        next_buffer[i] = mshr_new_miss;
                    end else begin
                        stall = 1;
                    end
                end else begin
                    if (!buffer[1].valid || bank_empty) begin
                        next_buffer[i] = '0;
                    end
                end
            end else if (i == MSHR_BUFFER_LEN - 1) begin
                if (bank_empty) begin
                    next_buffer[i] = buffer_copy[i - 1];
                end else begin
                    next_buffer[i] = buffer_copy[i];
                end
            end else begin
                if (!buffer[i + 1].valid || bank_empty) begin
                    next_buffer[i] = buffer_copy[i - 1];
                end
            end
        end    
    end

endmodule
