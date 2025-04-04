`include "cache_types_pkg.svh";

module cache_bank_pipe_lru (
    input logic CLK, nRST,
    input logic [BANKS_LEN-1:0] bank_id, // for requesting RAM
    input logic instr_valid, // valid single-cycle request 
    input logic [CACHE_RW_SIZE-1:0] ram_mem_data, // data incoming from RAM
    input mshr_reg mshr_entry,
    input in_mem_instr mem_instr_in,
    input logic ram_mem_complete, // RAM completed operation
    input logic halt, 
    output logic cache_bank_busy, // High when MSHR in-flight
    output logic scheduler_hit,
    output logic ram_mem_REN, 
    output logic ram_mem_WEN,
    output logic [CACHE_RW_SIZE-1:0] ram_mem_store, 
    output addr_t ram_mem_addr,
    output logic [31:0] scheduler_data_out,
    output logic [UUID_SIZE-1:0] scheduler_uuid_out,
    output logic scheduler_uuid_ready, 
    output logic flushed
);

    logic wrong_state;
    cache_set [NUM_SETS_PER_BANK-1:0] bank, next_bank;

    // FSM
    bank_fsm_states curr_state, next_state; 
    logic [BLOCK_OFF_BIT_LEN-1:0] count_FSM, next_count_FSM;
    logic count_flush;
    cache_frame latched_block_pull_buffer, latched_victim_eject_buffer;
    logic [NUM_BLOCKS_PER_BANK_LEN:0] flush_count, next_flush_count;
    logic [WAYS_LEN-1:0] latched_victim_way_index, victim_way_index, hit_way_index, next_flush_way, flush_way;
    logic [BLOCK_INDEX_BIT_LEN-1:0] latched_victim_set_index, set_index, victim_set_index, next_flush_set, flush_set; 

    // LRU 
    /////////////////////////////////////////////////////////////////////////////

    localparam AGE_WIDTH       = 32;
    localparam NUM_SETS        = NUM_SETS_PER_BANK;
    localparam SET_INDEX_WIDTH = $clog2(NUM_SETS);

    typedef enum logic [1:0] {
        LRU_IDLE,
        LRU_PROCESS,
        LRU_DONE
    } lru_state_t;
    
    lru_state_t    lru_state, lru_next_state;
    logic [SET_INDEX_WIDTH-1:0] set_counter, next_set_counter;

    lru_frame lru, next_lru;

    lru_frame lru_work [NUM_SETS-1:0];
    lru_frame updated_frame;

    logic [AGE_WIDTH-1:0] new_age [NUM_WAYS-1:0];
    logic [AGE_WIDTH-1:0] max_age;
    logic [WAYS_LEN-1:0]  max_way;

    logic lru_update_req;
    assign lru_update_req = (scheduler_hit || (curr_state == FINISH));

    assign cache_bank_busy = ((curr_state != FINISH) || (lru_state != LRU_IDLE));

    integer i, j;
    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            lru_state   <= LRU_IDLE;
            set_counter <= '0;
            lru_work[i] <= '0;
            lru <= '0;
        end else begin
            lru_state   <= lru_next_state;
            set_counter <= next_set_counter;
            // In LRU_IDLE, grab current LRU
            if (lru_state == LRU_IDLE && lru_update_req) begin
                for (i = 0; i < NUM_SETS; i++) begin
                lru_work[i] <= lru[i];
                end
            end
            // In LRU_PROCESS, change iwth update frame
            else if (lru_state == LRU_PROCESS) begin
                lru_work[set_counter] <= updated_frame;
            end
            // In LRU_DONE, put working copy back 
            if (lru_state == LRU_DONE) begin
                for (i = 0; i < NUM_SETS; i++) begin
                lru[i] <= lru_work[i];
                end
            end
        end
    end

    always_comb begin
        lru_next_state = lru_state;
        next_set_counter = set_counter;
        case (lru_state)
        LRU_IDLE: begin
            if (lru_update_req) lru_next_state = LRU_PROCESS;
        end
        LRU_PROCESS: begin
            if (set_counter == NUM_SETS - 1) lru_next_state = LRU_DONE;
            else next_set_counter = set_counter + 1;
        end
        LRU_DONE: begin
            lru_next_state = LRU_IDLE;
        end
        default: lru_next_state = LRU_IDLE;
        endcase
    end

    always_comb begin
        updated_frame = lru_work[set_counter];
        max_age = 0;
        max_way = 0;
        for (j = 0; j < NUM_WAYS; j++) begin
            if ((scheduler_hit && (set_counter == mem_instr_in.addr.index) && (j == hit_way_index)) ||
                (!scheduler_hit && (set_counter == mshr_entry.block_addr.index) && (j == lru_work[mshr_entry.block_addr.index].lru_way)))
                new_age[j] = 0;
            else
                new_age[j] = lru_work[set_counter].age[j] + 1;

            if (new_age[j] > max_age) begin
                max_age = new_age[j];
                max_way = j;  
            end
        end

        for (j = 0; j < NUM_WAYS; j++) begin
            updated_frame.age[j] = new_age[j];
        end

        updated_frame.lru_way = max_way;
    end


    /////////////////////////////////////////////////////////////////////////////

    always_ff @ (posedge CLK, negedge nRST) begin : sequential_update
        if (!nRST) begin 
            curr_state <= START;
            bank <= '0; 
            lru <= '0; 
            count_FSM <= '0;
            latched_victim_way_index <= '0; 
            latched_victim_set_index <= '0; 
            latched_victim_eject_buffer <= '0;
            latched_block_pull_buffer <= '0;
            flush_set <= '0; 
            flush_way <= '0;
            flush_count <= '0; 
        end else begin 
            curr_state <= next_state; 
            bank <= next_bank; 
            lru <= next_lru;
            flush_set <= next_flush_set; 
            flush_way <= next_flush_way;
            flush_count <= next_flush_count; 
            count_FSM <= next_count_FSM; 

            if (curr_state == START) begin
                if (mshr_entry.valid) begin 
                    latched_victim_set_index <= victim_set_index;
                    latched_victim_way_index <= victim_way_index;
                    latched_victim_eject_buffer <= bank[victim_set_index][victim_way_index];

                    latched_block_pull_buffer.valid <= 1'b1;
                    latched_block_pull_buffer.dirty <= 1'b1;
                    latched_block_pull_buffer.tag <= mshr_entry.block_addr.tag;
                end else begin 
                    latched_victim_set_index <= '0;
                    latched_victim_way_index <= '0;
                    latched_victim_eject_buffer <= '0;
                end 
            end else if ((curr_state == BLOCK_PULL)) begin 
                if (mshr_entry.write_status[count_FSM]) begin 
                    latched_block_pull_buffer.block[count_FSM] <= mshr_entry.write_block[count_FSM];
                end else if (ram_mem_complete) begin 
                    latched_block_pull_buffer.block[count_FSM] <= ram_mem_data;
                end 
            end
        end 
    end 


    always_comb begin : cache_controller_logic
        count_flush = 1'b0; 
        scheduler_uuid_out = '0; 
        ram_mem_REN = 1'b0; 
        ram_mem_WEN = 1'b0; 
        ram_mem_store = '0; 
        ram_mem_addr = '0; 
        next_bank = bank; 
        scheduler_hit = 1'b0; 
        scheduler_data_out = '0;
        hit_way_index = '0; 
        wrong_state = 1'b0; 
        scheduler_uuid_ready = 0;
        next_flush_set = flush_set; 
        next_flush_count = flush_count;
        next_flush_set = flush_set; 
        next_flush_way = flush_way; 

        if (instr_valid) begin
            for (int i = 0; i < NUM_WAYS; i++) begin 
                if (bank[set_index][i].valid && (bank[set_index][i].tag == mem_instr_in.addr.tag)) begin
                    if (mem_instr_in.rw_mode) begin
                        next_bank[set_index][i].block[mem_instr_in.addr.block_offset] = mem_instr_in.store_value;
                        next_bank[set_index][i].dirty = 1;
                    end else begin
                        scheduler_data_out = bank[set_index][i].block[mem_instr_in.addr.block_offset];
                    end
                    scheduler_hit = 1'b1;
                    hit_way_index = WAYS_LEN'(i);
                end
            end 
        end 

        case (curr_state) 
            START: begin 
                count_flush = 1; 
                if (mshr_entry.valid) begin 
                    next_bank[victim_set_index][victim_way_index].valid = 1'b0;
                end
            end 
            BLOCK_PULL: begin 
                ram_mem_REN = 1;
                ram_mem_addr = addr_t'{mshr_entry.block_addr.tag, latched_victim_set_index, BLOCK_INDEX_BIT_LEN'(count_FSM), BYTE_OFF_BIT_LEN'('0)};
                
                if ((count_FSM == BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1)) && ram_mem_complete) count_flush = 1'b1; 
            end 
            VICTIM_EJECT: begin 
                ram_mem_WEN = 1'b1; 
                ram_mem_addr = addr_t'{latched_victim_eject_buffer.tag, latched_victim_set_index, BLOCK_INDEX_BIT_LEN'(count_FSM), BYTE_OFF_BIT_LEN'('0)};
                ram_mem_store = latched_victim_eject_buffer.block[count_FSM];

                if ((count_FSM == BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1)) && ram_mem_complete) count_flush = 1'b1; 
            end
            FINISH: begin 
                next_bank[latched_victim_set_index][latched_victim_way_index].valid = 1'b1; 
                next_bank[latched_victim_set_index][latched_victim_way_index].dirty = |mshr_entry.write_status; 
                next_bank[latched_victim_set_index][latched_victim_way_index].tag = mshr_entry.block_addr.tag; 
                next_bank[latched_victim_set_index][latched_victim_way_index].block = latched_block_pull_buffer.block; 
                scheduler_uuid_out = mshr_entry.uuid;
                scheduler_uuid_ready = 1;
            end
            FLUSH: begin 
                if (next_state != WRITEBACK) begin 
                    next_flush_set = BLOCK_INDEX_BIT_LEN'(flush_count);
                    if (flush_set == (NUM_SETS_PER_BANK - 1)) next_flush_way = flush_way + 1; 
                    if (!bank[flush_set][flush_way].dirty) next_flush_count = flush_count + 1; 
                end 
            end 
            WRITEBACK: begin 
                ram_mem_WEN = 1'b1; 
                ram_mem_addr = addr_t'{bank[next_flush_set][next_flush_way].tag, next_flush_set, BLOCK_INDEX_BIT_LEN'(count_FSM), BYTE_OFF_BIT_LEN'('0)};
                ram_mem_store = bank[next_flush_set][next_flush_way].block[BLOCK_INDEX_BIT_LEN'(count_FSM)];

                if (ram_mem_complete) begin 
                    if (count_FSM == BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1)) begin 
                        count_flush = 1'b1; 
                        next_bank[next_flush_set][next_flush_way].dirty = 1'b0;
                        next_bank[next_flush_set][next_flush_way].valid = 1'b0;
                        next_bank[next_flush_set][next_flush_way].block = '0; // Don't really need this? 
                    end  
                end 
        
            end
            HALT: flushed = 1; 
        endcase
    end 

    always_comb begin : fsm_state_logic
        next_state = curr_state; 
        case (curr_state) 
            START: begin 
                if (mshr_entry.valid) next_state = BLOCK_PULL;
                else if (halt) next_state = FLUSH; 
            end 
            BLOCK_PULL:  if (count_FSM == (BLOCK_SIZE - 1) && (next_count_FSM == 0)) next_state = (bank[latched_victim_set_index][latched_victim_way_index].dirty) ? VICTIM_EJECT : FINISH;  
            VICTIM_EJECT: if (count_FSM == (BLOCK_SIZE - 1) && (next_count_FSM == 0)) next_state = FINISH; 
            FINISH: next_state = START; 
            FLUSH: begin 
                if (flush_count == (NUM_BLOCKS_PER_BANK + 1)) next_state = HALT;
                else if (bank[flush_set][flush_way].dirty) next_state = WRITEBACK;
            end
            WRITEBACK: if (count_FSM == (BLOCK_SIZE - 1) && (next_count_FSM == 0)) next_state = FLUSH; 
            HALT: next_state = START; 
            default: next_state = START;  
        endcase
    end 

endmodule
