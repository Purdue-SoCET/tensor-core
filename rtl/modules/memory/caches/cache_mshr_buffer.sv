/*  Vinay Jagan - vjagan@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

import caches_pkg::*;

module cache_mshr_buffer (
    input logic CLK, nRST,
    input logic miss,
    input logic [BANKS_LEN-1:0] bank_id,
    input in_mem_instr mem_instr,
    input logic bank_free,
    output mshr_reg mshr_out,
    output logic stall, 
    output logic [UUID_SIZE-1:0] uuid_out, 
    output logic buffer_empty
);
    mshr_reg [MSHR_BUFFER_LEN-1:0] buffer, next_buffer;
    logic [MSHR_BUFFER_LEN-2:0] secondary_misses;
    mshr_reg mshr_new_miss;
    logic [UUID_SIZE-1:0] uuid, next_uuid;

    logic [MSHR_BUFFER_BIT_LEN-1:0] lptr, rptr, next_lptr, next_rptr;


    always_comb begin
        mshr_new_miss.valid = miss;
        next_uuid = uuid;

        uuid_out = 0;

        if (miss && !stall) begin 
            next_uuid = uuid + 1;
            uuid_out = uuid;
            mshr_new_miss.uuid = uuid;
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
            lptr <= MSHR_BUFFER_LEN - 1;
            rptr <= MSHR_BUFFER_LEN - 1;
        end else begin
            buffer <= next_buffer;
            uuid <= next_uuid;
            
            lptr <= next_lptr;
            rptr <= next_rptr;
        end
    end

    always_comb begin
        next_lptr = lptr;
        next_rptr = rptr;
        stall = 0;

        if (bank_free && buffer[rptr].valid) begin
            next_rptr = rptr - 1;
        end
        if (miss && secondary_misses == 0) begin
            if (lptr != rptr || (bank_free && buffer[rptr].valid) || !buffer[rptr].valid) begin
                next_lptr = lptr - 1;
            end else begin
                stall = 1;
            end
        end
    end

    always_comb begin
        secondary_misses = 0;
        next_buffer = buffer;
        mshr_out = buffer[rptr];

        if (miss) begin
            for (int i = 0; i < MSHR_BUFFER_LEN - 1; i++) begin
                if (i != rptr && buffer[i].block_addr == mshr_new_miss.block_addr && buffer[i].valid) begin
                    secondary_misses[i] = 1;
                    next_buffer[i].write_status = buffer[i].write_status | mshr_new_miss.write_status;
                    next_buffer[i].write_block[mem_instr.addr.block_offset] =  (mem_instr.rw_mode) ? mem_instr.store_value : buffer[i].write_block[mem_instr.addr.block_offset];
                    next_buffer[i].uuid = uuid;
                end
            end
            if (secondary_misses == 0) begin
                next_buffer[lptr] = mshr_new_miss;
            end
        end

        if (bank_free && buffer[rptr].valid) begin
            next_buffer[rptr].valid = 0;
        end
    end

    always_comb begin
        buffer_empty = 1; 
        for (int j = 0; j < MSHR_BUFFER_LEN; j++) begin
            if (buffer[j].valid) begin
                buffer_empty = 0;
            end
        end
    end

endmodule