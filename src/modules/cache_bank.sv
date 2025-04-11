`include "cache_types_pkg.svh";

module cache_bank (
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

    cache_set [NUM_SETS_PER_BANK-1:0] bank, next_bank;
    logic mshr_hit, next_mshr_hit;

    // FSM
    bank_fsm_states curr_state, next_state; 
    logic [NUM_BLOCKS_LEN-1:0] count_FSM, next_count_FSM;
    logic count_flush;
    cache_frame latched_block_pull_buffer, latched_victim_eject_buffer;
    logic [NUM_BLOCKS_PER_BANK_LEN:0] flush_count, next_flush_count;
    logic [WAYS_LEN-1:0] latched_victim_way_index, victim_way_index, hit_way_index, max_way, next_flush_way, flush_way, mshr_hit_way;
    logic [BLOCK_INDEX_BIT_LEN-1:0] latched_victim_set_index, set_index, victim_set_index, next_flush_set, flush_set; 

    // LRU 
    psuedo_lru_frame [NUM_SETS_PER_BANK-1:0] tree_lru, next_tree_lru;  
    logic [TREE_BITS-1:0] _node, __node;

    assign set_index = mem_instr_in.addr.index >> BANKS_LEN;    
    assign victim_set_index = mshr_entry.block_addr.index >> BANKS_LEN; 

    always_ff @ (posedge CLK, negedge nRST) begin : sequential_update
        if (!nRST) begin 
            curr_state <= START;
            bank <= '0; 
            tree_lru <= '0; 
            count_FSM <= '0;
            latched_victim_way_index <= '0; 
            latched_victim_set_index <= '0; 
            latched_victim_eject_buffer <= '0;
            latched_block_pull_buffer <= '0;
            flush_set <= '0; 
            flush_way <= '0;
            flush_count <= '0;
            mshr_hit <= 0;
        end else begin 
            curr_state <= next_state; 
            bank <= next_bank; 
            tree_lru <= next_tree_lru;
            flush_set <= next_flush_set; 
            flush_way <= next_flush_way;
            flush_count <= next_flush_count; 
            count_FSM <= next_count_FSM; 
            mshr_hit <= next_mshr_hit;

            if (curr_state == START) begin
                if (mshr_entry.valid) begin 
                    latched_victim_set_index <= victim_set_index;
                    latched_victim_way_index <= (next_mshr_hit) ? mshr_hit_way : victim_way_index;
                    latched_victim_eject_buffer <= bank[victim_set_index][victim_way_index];

                    latched_block_pull_buffer.valid <= 1'b1;
                    latched_block_pull_buffer.dirty <= (|mshr_entry.write_status || (mshr_hit && bank[latched_victim_set_index][latched_victim_way_index].dirty));
                    latched_block_pull_buffer.tag <= mshr_entry.block_addr.tag;
                end else begin 
                    latched_victim_set_index <= '0;
                    latched_victim_way_index <= '0;
                    latched_victim_eject_buffer <= '0;
                end 
            end else if ((curr_state == BLOCK_PULL)) begin 
                if (mshr_entry.write_status[NUM_BLOCKS_LEN'(count_FSM)]) begin 
                    latched_block_pull_buffer.block[NUM_BLOCKS_LEN'(count_FSM)] <= mshr_entry.write_block[NUM_BLOCKS_LEN'(count_FSM)];
                end else if (ram_mem_complete && !mshr_hit) begin 
                    latched_block_pull_buffer.block[NUM_BLOCKS_LEN'(count_FSM)] <= ram_mem_data;
                end 
            end
        end 
    end 

    always_comb begin : check_mshr_hit
        next_mshr_hit = 0;
        mshr_hit_way = 0;

        if (mshr_entry.valid && curr_state != FINISH) begin
            for (int i = 0; i < NUM_WAYS; i++) begin
                if (mshr_entry.block_addr.tag == bank[victim_set_index][i].tag && bank[victim_set_index][i].valid) begin
                    next_mshr_hit = 1'b1;
                    mshr_hit_way = i;
                end 
            end
        end
    end

    always_comb begin : do_count_FSM
        next_count_FSM = count_FSM;
        if (count_flush) next_count_FSM = 0; 
        else if (((ram_mem_complete && !mshr_hit) || mshr_hit || ((mshr_entry.write_status[count_FSM] && (count_FSM != (BLOCK_SIZE - 1)))))) next_count_FSM = count_FSM + 1; 
    end

    always_comb begin : tree_based_lru_update
        next_tree_lru = tree_lru;
        _node = 0; 
        __node = 0; 

        for (int level = 0; level < WAYS_LEN; level++) begin
            if (tree_lru[victim_set_index].tree[__node] == 0) begin
                victim_way_index[WAYS_LEN-1 - level] = 0;
                __node = (2 * __node) + 1;
            end else begin
                victim_way_index[WAYS_LEN-1 - level] = 1;
                __node = (2 * __node) + 2;
            end

            if (scheduler_hit) begin
                next_tree_lru[set_index].tree[_node] = ~hit_way_index[(WAYS_LEN-1) - level];

                if (!hit_way_index[(WAYS_LEN-1) - level]) _node = (2 * _node) + 1;
                else _node = (2 * _node) + 2;
            end
            else if (curr_state == FINISH) begin
                next_tree_lru[latched_victim_set_index].tree[_node] = ~latched_victim_way_index[WAYS_LEN-1 - level];

                if (!latched_victim_way_index[WAYS_LEN-1 - level]) _node = (2 * _node) + 1;
                else _node = (2 * _node) + 2;
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
        scheduler_uuid_ready = 0;
        cache_bank_busy = 0;
        next_flush_count = flush_count;
        next_flush_set = flush_set; 
        next_flush_way = flush_way; 
        flushed = 0; 

        if (instr_valid) begin
            for (int i = 0; i < NUM_WAYS; i++) begin 
                if (!scheduler_hit) begin 
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
        end 

        case (curr_state) 
            START: begin 
                count_flush = 1; 
                if (mshr_entry.valid) begin 
                    next_bank[victim_set_index][victim_way_index].valid = 1'b0;
                    cache_bank_busy = 1; 
                end
            end 
            BLOCK_PULL: begin 
                cache_bank_busy = 1; 

                ram_mem_REN = !mshr_hit && !mshr_entry.write_status[NUM_BLOCKS_LEN'(count_FSM)];
                ram_mem_addr = addr_t'{mshr_entry.block_addr.tag, ((latched_victim_set_index  << BANKS_LEN) | bank_id), BLOCK_OFF_BIT_LEN'(count_FSM), BYTE_OFF_BIT_LEN'('0)};
            end 
            VICTIM_EJECT: begin 
                cache_bank_busy = 1; 

                ram_mem_WEN = 1'b1; 
                ram_mem_addr = addr_t'{latched_victim_eject_buffer.tag, ((latched_victim_set_index  << BANKS_LEN) | bank_id), NUM_BLOCKS_LEN'(count_FSM), BYTE_OFF_BIT_LEN'('0)};
                ram_mem_store = latched_victim_eject_buffer.block[count_FSM];
            end
            FINISH: begin 
                cache_bank_busy = 0;
                next_bank[latched_victim_set_index][latched_victim_way_index] = latched_block_pull_buffer; 
                scheduler_uuid_out = mshr_entry.uuid;
                scheduler_uuid_ready = 1;
            end
            FLUSH: begin 
                if (next_state != WRITEBACK) begin 
                    next_flush_set = NUM_SETS_PER_BANK_LEN'(flush_count);
                    if (flush_set == (NUM_SETS_PER_BANK - 1)) next_flush_way = flush_way + 1; 
                    if (!bank[flush_set][flush_way].dirty) next_flush_count = flush_count + 1; 
                end 
            end 
            WRITEBACK: begin 
                ram_mem_WEN = 1'b1; 
                ram_mem_addr = addr_t'{bank[next_flush_set][next_flush_way].tag, ((next_flush_set  << BANKS_LEN) | bank_id), NUM_BLOCKS_LEN'(count_FSM), BYTE_OFF_BIT_LEN'('0)};
                ram_mem_store = bank[next_flush_set][next_flush_way].block[NUM_BLOCKS_LEN'(count_FSM)];

                if (ram_mem_complete) begin 
                    if (count_FSM == NUM_BLOCKS_LEN'(BLOCK_SIZE - 1)) begin 
                        count_flush = 1'b1; 
                        next_bank[next_flush_set][next_flush_way].dirty = 1'b0;
                        next_bank[next_flush_set][next_flush_way].valid = 1'b0;
                        next_bank[next_flush_set][next_flush_way].block = '0;
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
            BLOCK_PULL:  if ((count_FSM == (BLOCK_SIZE - 1)) && (next_count_FSM == 0)) next_state = (bank[latched_victim_set_index][latched_victim_way_index].dirty && !mshr_hit) ? VICTIM_EJECT : FINISH;  
            VICTIM_EJECT: if (count_FSM == (BLOCK_SIZE - 1) && (next_count_FSM == 0)) next_state = FINISH; 
            FINISH: next_state = START; 
            FLUSH: begin 
                if (flush_count == (NUM_BLOCKS_PER_BANK + 1)) next_state = HALT;
                else if (bank[flush_set][flush_way].dirty) next_state = WRITEBACK;
            end
            WRITEBACK: if (count_FSM == (BLOCK_SIZE - 1) && (next_count_FSM == 0)) next_state = FLUSH; 
            HALT: next_state = HALT; 
        endcase
    end 

endmodule
