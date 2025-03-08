`include "cache_types_pkg.svh";

module cache_mshr_buffer (
    input logic CLK, nRST,
    input logic miss,
    input in_mem_instr mem_instr,
    input logic bank_empty,
    output mshr_reg mshr_out,
    output logic stall
);
    mshr_reg [MSHR_BUFFER_LEN-1:0] buffer, next_buffer;
    mshr_reg [MSHR_BUFFER_LEN-2:0] buffer_copy;
    logic [MSHR_BUFFER_LEN-2:0] secondary_misses;

    mshr_reg mshr_new_miss;
    always_comb begin
        mshr_new_miss.valid = miss;
        mshr_new_miss.uuid = mem_instr.uuid;
        mshr_new_miss.block_addr = {mem_instr.addr.tag, mem_instr.addr.index, BLOCK_OFF_BIT_LEN'(0), BYTE_OFF_BIT_LEN'(0)};
        mshr_new_miss.write_status = 0;
        mshr_new_miss.write_status[mem_instr.addr.block_offset] = mem_instr.rw_mode;
        mshr_new_miss.write_block = 0;
        mshr_new_miss.write_block[mem_instr.addr.block_offset] = mem_instr.store_value;
    end


    always_ff @( posedge CLK, negedge nRST ) begin
        if (!nRST) begin
            buffer <= 0;
        end else begin
            buffer <= next_buffer;
        end
    end

    genvar i;
    generate
        for (i = 0; i < MSHR_BUFFER_LEN - 1; i++) begin
            always_comb begin
                buffer_copy[i] = buffer[i];
                secondary_misses[i] = 0;
                if (mshr_new_miss.valid && buffer[i].block_addr == mshr_new_miss.block_addr && buffer[i].valid) begin
                    buffer_copy[i].write_status = buffer[i].write_status | mshr_new_miss.write_status;
                    buffer_copy[i].write_block[mem_instr.addr.block_offset] =  (mem_instr.rw_mode) ? mem_instr.store_value : buffer[i].write_block[mem_instr.addr.block_offset];
                    secondary_misses[i] = 1;
                end
            end
        end
    endgenerate

    genvar j;
    generate
        for (j = 1; j < MSHR_BUFFER_LEN; j++) begin
            always_comb begin
                if (!buffer[j].valid || bank_empty) begin
                    next_buffer[j] = buffer_copy[j - 1];
                end else begin
                    next_buffer[j] = buffer[j];
                end
            end
        end
    endgenerate

    always_comb begin
        stall = 0;
        mshr_out = buffer[MSHR_BUFFER_LEN - 1];
        next_buffer[0] = buffer_copy[0];

        if ((secondary_misses == 0) && mshr_new_miss.valid) begin
            if (!buffer[0].valid || bank_empty) begin
                next_buffer[0] = mshr_new_miss;
            end else begin
                stall = 1;
            end
        end else begin
            if (buffer[1].valid || bank_empty) begin
                next_buffer[0] = 0;
            end
        end

    end

endmodule
