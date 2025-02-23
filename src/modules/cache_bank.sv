`include "cache_types_pkg.svh";

module cache_bank (
    input logic CLK, nRST,
    input logic [BLOCK_INDEX_BIT_LEN-1:0] bank_index, // for requesting RAM
    input logic instr_valid, // valid single-cycle request 
    input logic [BLOCK_SIZE-1:0][31:0] scheduler_data_in, // data coming in for single-cycle scheduler_hit 
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
    output logic [3:0] scheduler_uuid_out
);

    typedef enum logic [2:0] { 
        START, BLOCK_PULL, VICTIM_EJECT, FINISH 
    } states; 

    cache_set [NUM_SETS_PER_BANK-1:0] bank, next_bank;
    logic [WAYS_LEN-1:0] victim_way, hit_way;  
    logic [INDEX_BIT_LEN-1:0] set_index, mshr_set_index; 
    cache_set chosen_set, next_chosen_set;
    cache_set mshr_chosen_set, next_mshr_chosen_set;
    logic is_valid; 

    logic [BLOCK_OFF_BIT_LEN-1:0] count_FSM;
    states curr_state, next_state; 
    logic count_enable; 
    logic count_flush; 

    logic [3:0] uuid_out;
    cache_block block_pull_buffer;
    cache_block victim_eject_buffer;

    logic [NUM_SETS-1:0][2:0] lru, next_lru;

    assign set_index = mem_instr_in.addr.block_offset >> NUM_BANKS; 
    assign chosen_set = bank[set_index];
    assign next_chosen_set = next_bank[set_index];

    assign mshr_set_index = mshr_entry.block_addr >> NUM_BANKS; 
    assign mshr_chosen_set = bank[mshr_set_index];
    assign next_mshr_chosen_set = next_bank[mshr_set_index];

    assign bank_ready = (curr_state != FINISH); // FINISH happens in a single cycle; MSHR Buffer sends in next cycle, and FINISH is also a single cycle state

    always_ff @ (posedge CLK, negedge nRST) begin : sequential_update
        if (!nRST) begin 
            curr_state <= START;
            bank <= '0; 
            block_pull_buffer[count_FSM] <= '0; 
            lru <= '0; 
        end else begin 
            curr_state <= next_state; 
            bank <= next_bank; 
            block_pull_buffer[count_FSM] <= ram_mem_data;
            lru <= next_lru;
        end 
    end 

    always_ff @(posedge CLK, negedge nRST) begin : counter
        if (!nRST) count_FSM <= '0;
        else if (count_enable && ram_mem_complete) count_FSM <= count_FSM + 1;
        else if (count_flush) count_FSM <= '0;
    end

    always_comb begin : tree_based_lru
        next_lru = lru; 

        if (scheduler_hit) begin : updating_lru
            case (hit_way) 
                2'd0: begin
                    next_lru[set_index][2] = 1'b0; 
                    next_lru[set_index][0] = 1'b0; 
                end
                2'd1: begin
                    next_lru[set_index][2] = 1'b0;
                    next_lru[set_index][0] = 1'b1; 
                end
                2'd2: begin
                    next_lru[set_index][2] = 1'b1; 
                    next_lru[set_index][1] = 1'b0; 
                end
                2'd3: begin
                    next_lru[set_index][2] = 1'b1;
                    next_lru[set_index][1] = 1'b1;
                end
            endcase
        end 

        if (curr_state == FINISH) begin 
            case (victim_way) 
                2'd0: begin
                    next_lru[mshr_set_index][2] = 1'b0; 
                    next_lru[mshr_set_index][0] = 1'b0; 
                end
                2'd1: begin
                    next_lru[mshr_set_index][2] = 1'b0;
                    next_lru[mshr_set_index][0] = 1'b1; 
                end
                2'd2: begin
                    next_lru[mshr_set_index][2] = 1'b1; 
                    next_lru[mshr_set_index][1] = 1'b0; 
                end
                2'd3: begin
                    next_lru[mshr_set_index][2] = 1'b1;
                    next_lru[mshr_set_index][1] = 1'b1;
                end
            endcase
        end

        if (count_FSM == BLOCK_SIZE - 2) begin : pull_lru
            if (lru[mshr_set_index][2] == 1'b0) begin 
                if (!lru[mshr_set_index][0]) victim_way = 2'd1;
                else victim_way = 2'd0;
            end else begin
                if (!lru[mshr_set_index][1]) victim_way = 2'd3;
                else victim_way = 2'd2;
            end
        end
    end

    always_comb begin : single_cycle_response
        next_bank = bank; 
        scheduler_hit = 1'b0; 
        scheduler_data_out = '0;

        if (instr_valid && (set_index != mshr_set_index)) begin // miss, if set-conflict
            for (int i = 0; i < NUM_WAYS; i++) begin 
                next_chosen_set[i].block[mem_instr_in.addr.block_offset] = chosen_set[i].block[mem_instr_in.addr.block_offset];
                if (chosen_set[i].valid && (chosen_set[i].tag == mem_instr_in.addr.tag)) begin : tag_checking
                    scheduler_hit = 1'b1; 
                    hit_way = i; 
                    
                    if (!mem_instr_in.rw_mode) begin : read
                        scheduler_data_out = (mshr_set_index != set_index) ? chosen_set[i].block[mem_instr_in.addr.block_offset] : block_pull_buffer[mem_instr_in.addr.block_offset];
                    else begin : write
                        next_chosen_set[i].block[mem_instr_in.addr.block_offset] = {1'b1, 1'b1, mem_instr_in.addr.tag, mem_instr_in.addr.store_value}; // dirty bit set
                        end 
                    end 

                end 
            end 
        end 
    end


    always_comb begin : cache_controller_logic
        count_flush = 1'b1; // unless BLOCK_PULL or VICTIM_EJECT
        count_enable = 1'b0;
        scheduler_uuid_out = '0; 
        ram_mem_REN = 1'b0; 
        ram_mem_WEN = 1'b0; 
        ram_mem_store = '0; 
        ram_mem_addr = '0; 
        victim_eject_buffer = victim_eject_buffer; // latched, reset at START

        // When START transitions to BLOCK_PULL, bank_busy goes high, and mshr_entry remains the same

        case (curr_state) 
            START: begin 
                victim_eject_buffer = '0; 
            end 
            BLOCK_PULL: begin 
                if (count_FSM == BLOCK_SIZE - 1) begin 
                    next_mshr_chosen_set[i].valid = 1'b0;  // invalidate current contents to ensure no concurrent read
                    victim_eject_buffer = next_mshr_chosen_set[victim_way].block; 
                    count_flush = 1'b1; 
                end

                count_flush = 1'b0; 

                if (ram_mem_complete || (count_FSM == 1)) count_enable = 1; 

                if (mshr_entry.write_status[count_FSM] == 1) ram_mem_WEN = 1;  
                else ram_mem_REN = 1;
                
                ram_mem_addr = mshr_entry.block_addr + count_FSM; 
                ram_mem_store = bank[mshr_entry.block_addr + count_FSM];                     
            end 
            VICTIM_EJECT: begin 
                if (count_FSM == BLOCK_SIZE - 1) begin : validate_new_frame 
                    next_mshr_chosen_set[victim_way].valid = 1'b1; 
                    next_mshr_chosen_set[victim_way].dirty = 1'b0; 
                    next_mshr_chosen_set[victim_way].tag = mshr_entry.tag; 
                    count_flush = 1'b1; 
                end 

                count_flush = 1'b0; 

                if (ram_mem_complete || (count_FSM == 1'b1)) count_enable = 1'b1; // off till RAM sends back data

                ram_mem_WEN = 1'b1; 
                
                // To RAM 
                ram_mem_store = victim_eject_buffer[count_FSM];
                ram_mem_addr  = {mshr_chosen_set[victim_way].tag, bank_index, mshr_entry.block_addr + count_FSM, 2'b00}; // rebuilding the block address, TODO: confirm this
                
                // Updating Bank, while valid = 0
                next_mshr_chosen_set[victim_way].block[mshr_entry.write_status[count_FSM]] = block_pull_buffer[count_FSM];
            end
            FINISH: scheduler_uuid_out = mshr_entry.uuid;
        endcase
    end 


    always_comb begin : fsm_state_logic
        next_state = curr_state; 
        case (curr_state) 
            START: if (instr_valid && mshr_entry.valid) next_state = BLOCK_PULL;
            BLOCK_PULL:  if (count_FSM == BLOCK_SIZE - 1) next_state = VICTIM_EJECT; 
            VICTIM_EJECT: if (count_FSM == BLOCK_SIZE - 1) next_state = FINISH; 
            FINISH: next_state = START; 
            default: next_state = START;  
        endcase
    end 

endmodule