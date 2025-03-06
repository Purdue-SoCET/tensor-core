`include "cache_types_pkg.svh";

module cache_bank (
    input logic CLK, nRST,
    input logic [BANKS_LEN-1:0] bank_id, // for requesting RAM
    input logic instr_valid, // valid single-cycle request 
    input logic [CACHE_RW_SIZE-1:0] ram_mem_data, // data incoming from RAM
    input mshr_reg mshr_entry,
    input in_mem_instr mem_instr_in,
    input logic ram_mem_complete, // RAM completed operation
    output logic cache_bank_busy, // High when MSHR in-flight
    output logic scheduler_hit,
    output logic ram_mem_REN, 
    output logic ram_mem_WEN,
    output logic [CACHE_RW_SIZE-1:0] ram_mem_store, 
    output logic [31:0] ram_mem_addr,
    output logic [31:0] scheduler_data_out,
    output logic [3:0] scheduler_uuid_out,
    output logic scheduler_uuid_ready
);

    typedef enum logic [2:0] { 
        START, BLOCK_PULL, VICTIM_EJECT, FINISH 
    } states; 

    logic [BLOCK_OFF_BIT_LEN-1:0] count_FSM;
    states curr_state, next_state; 
    logic count_enable; 
    logic count_flush; 
    logic wrong_state; // Debugging?

    cache_frame latched_block_pull_buffer;
    cache_frame latched_victim_eject_buffer;
    
    cache_set [NUM_SETS_PER_BANK-1:0] bank, next_bank;
    
    logic [WAYS_LEN-1:0] latched_victim_way_index, victim_way_index, hit_way_index;  
    logic [BLOCK_INDEX_BIT_LEN-1:0] latched_victim_set_index, set_index, victim_set_index; 

    lru_frame [NUM_SETS_PER_BANK-1:0] lru, next_lru;
    

    assign set_index = mem_instr_in.addr.index >> BANKS_LEN;    
    assign victim_set_index = mshr_entry.block_addr.index >> BANKS_LEN; 
    assign victim_way_index = lru[victim_set_index].lru_way;

    always_ff @ (posedge CLK, negedge nRST) begin : sequential_update
        if (!nRST) begin 
            curr_state <= START;
            bank <= '0; 
            lru <= '0; 
            latched_victim_way_index <= '0; 
            latched_victim_set_index <= '0; 
            latched_victim_eject_buffer <= '0;
            latched_block_pull_buffer <= '0;
        end else begin 
            curr_state <= next_state; 
            bank <= next_bank; 
            lru <= next_lru;
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
                    latched_victim_eject_buffer <= '0;
                end
            end else if ((curr_state == BLOCK_PULL) && (ram_mem_complete || (count_FSM == 0))) begin 
                latched_block_pull_buffer.block[count_FSM] <= ram_mem_data;
            end 
        end 
    end 

    always_ff @(posedge CLK, negedge nRST) begin : counter
        if (!nRST) count_FSM <= '0;
        else if (count_enable) count_FSM <= count_FSM + 1;
        else if (count_flush) count_FSM <= '0;
        else count_FSM <= count_FSM;
    end

   always_comb begin : age_based_lru
        next_lru = lru; 

        if (scheduler_hit || (curr_state == FINISH)) begin
            for (int i = 0; i < NUM_SETS_PER_BANK; i++) begin
                for (int j = 0; j <= NUM_WAYS - 1; j++) begin
                    next_lru[i].age[j] = lru[i].age[j] + 1; 
                    if (lru[i].age[lru[i].lru_way] < lru[i].age[j]) begin
                        next_lru[i].lru_way = j[WAYS_LEN-1:0];
                    end
                end
            end

            if (scheduler_hit) begin
                next_lru[set_index].age[hit_way_index] = 0;
            end
            
            if (curr_state == FINISH) begin
                next_lru[latched_victim_set_index].age[latched_victim_way_index] = 0;
            end
        end
    end


    always_comb begin : cache_controller_logic
        count_flush = 1'b1; 
        count_enable = 1'b0;
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
        cache_bank_busy = 0;

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
            default: wrong_state = 1'b1; 
            START: begin 
                if (mshr_entry.valid) begin 
                    next_bank[latched_victim_set_index][latched_victim_way_index].valid = 1'b0;
                    cache_bank_busy = 1; 
                end
            end 
            BLOCK_PULL: begin 
                cache_bank_busy = 1; 
                if (count_FSM != (BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1))) count_flush = 1'b0; 


                if (ram_mem_complete) begin
                    count_enable = 1'b1;
                end

                ram_mem_REN = 1;
                ram_mem_addr = {mshr_entry.block_addr.tag, mshr_entry.block_addr.index, BLOCK_INDEX_BIT_LEN'(count_FSM), 2'b0};
            end 
            VICTIM_EJECT: begin 
                cache_bank_busy = 1; 
                if (count_FSM != BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1)) count_flush = 1'b0; 

                if (ram_mem_complete) begin
                    count_enable = 1'b1;
                end

                ram_mem_WEN = 1'b1; 
                ram_mem_addr = {latched_victim_eject_buffer.tag, latched_victim_set_index << BANKS_LEN, BLOCK_INDEX_BIT_LEN'(count_FSM), 2'b0};
                ram_mem_store = latched_victim_eject_buffer.block[count_FSM];
            end
            FINISH: begin 
                cache_bank_busy = 0;
                next_bank[latched_victim_set_index][latched_victim_way_index].valid = 1'b1; 
                next_bank[latched_victim_set_index][latched_victim_way_index].dirty = |mshr_entry.write_status; 
                next_bank[latched_victim_set_index][latched_victim_way_index].tag = mshr_entry.block_addr.tag; 
                next_bank[latched_victim_set_index][latched_victim_way_index].block = latched_block_pull_buffer.block; 
                scheduler_uuid_out = mshr_entry.uuid;
                scheduler_uuid_ready = 1;
            end
        endcase
    end 


    always_comb begin : fsm_state_logic
        next_state = curr_state; 
        case (curr_state) 
            START: if (mshr_entry.valid) next_state = BLOCK_PULL;
            BLOCK_PULL:  if (count_FSM == BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1)) next_state = VICTIM_EJECT; 
            VICTIM_EJECT: if (count_FSM == BLOCK_OFF_BIT_LEN'(BLOCK_SIZE - 1)) next_state = FINISH; 
            FINISH: next_state = START; 
            default: next_state = START;  
        endcase
    end 



endmodule
