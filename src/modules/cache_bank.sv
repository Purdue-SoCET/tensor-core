`include "cache_types_pkg.svh";

module cache_bank (
    input logic CLK, nRST,
    input logic instr_valid,
    input logic mshr_valid,
    input logic load, store, next_load, next_store, 
    input logic [BLOCK_SIZE-1:0][31:0] mem_data_in,
    input logic [CACHE_RW_SIZE-1:0] load_data, store_data, 
    input mshr_reg mshr_entry,
    input in_mem_instr mem_instr_in,
    input addr_t load_addr, store_addr, next_load_addr, next_store_addr,
    output logic bank_empty,
    output logic hit,
    output logic dmemREN, 
    output logic dmemWEN,
    output logic dmemstore, 
    output logic dmemaddr,
    output logic [31:0] data_out,
    output logic [3:0] uuid_out

);

    // TODO: 
    // 1. Write the read part of the FSM - write_status 
    // 2. Write the write part of the FSM - write_status and write_block
    // 3. Do the block.dirty stuff
    // 3. Verify addr path is right
    // 4. Verify right data is going through
    // 5. Verify the mem stuff with William 

    typedef enum logic [2:0] { 
        START, BLOCK_PULL, VICTIM_EJECT, FINISH 
    } states; 

    cache_set bank [NUM_SETS_PER_BANK-1:0];
    logic [NUM_WAYS-1:0] victim_way, hit_way;  
    logic is_valid; 
    logic [3:0] internal_mshr; 
    logic [BLOCK_OFF_BIT_LEN-1:0] count_BLOCK_PULL;
    logic [BLOCK_OFF_BIT_LEN-1:0] count_VICTIM_EJECT;
    states curr_state, next_state; 

    assign set_index_in_bank = mem_instr_in.addr.block_offset >> NUM_BANKS; 
    assign chosen_set = dcache[set_index];
    assign uuid_out = (internal_mshr && (curr_state == FINISH)) ? internal_mshr.uuid : '0; 

    always_ff @ (posedge CLK, negedge nRST) begin : seq_fsm
        if (!nRST) begin 
            curr_state <= START;
            bank_ready <= 1'b0; 
        end else begin 
            curr_state <= next_state; 
            if (mshr_valid) bank_ready <= 1'b1;
            else if (curr_state == FINISH) bank_ready <= 1'b0;
        end 
    end 


    // if there is at least one invalidated way, then we set bank_empty = 1; 
    // MSHR will stall if there is no invalidated way whcih can be replaced
    always_comb begin : bank_empty 
        bank_empty = 0; 
        for (int i = 0; i < NUM_SETS_PER_BANK; i++) begin 
            for (int j = 0; j < NUM_WAYS; j++) begin 
                if (!dcache[i][j].valid) bank_empty = 1; break; 
            end 
        end 
    end 

    always_ff @(posedge CLK, negedge nRST) begin : count_block_pull
        if (nRST) count_BLOCK_PULL <= (BLOCK)'d0;
        else if ((curr_state == BLOCK_PULL) && ram_confirmed) count_BLOCK_PULL <= count_BLOCK_PULL + 1;
        else count_BLOCK_PULL <= (BLOCK)'d0;
    end

    always_ff @(posedge CLK, negedge nRST) begin : count_victim_eject
        if (nRST) count_VICTIM_EJECT <= (BLOCK)'d0;
        else if ((curr_state == VICTIM_EJECT) && ram_confirmed) count_VICTIM_EJECT <= count_VICTIM_EJECT + 1;
        else count_VICTIM_EJECT <= (BLOCK)'d0;
    end

    always_comb begin : single_cycle_response
        hit = 1'b0; 
        for (int i = 0; i < NUM_WAYS; i++) begin 
            is_valid = chosen_set[i].valid; 
            if (curr_state == START && victim_way == i) begin : invalidating_victim
                hit = 1'b0; 
                is_valid = 1'b0; 
            end 
            if (is_valid && (chosen_set[i].tag == tag)) begin : tag_checking
                hit = 1'b1; 
                if (!mem_instr_in.rw_mode) begin 
                    data_out = chosen_set[i].block[mem_instr_in.addr.block_offset];
                else begin 
                    chosen_set[i].block[mem_instr_in.addr.block_offset] = mem_instr_in.addr.store_value;
                    chosen_set[i].block[mem_instr_in.addr.block_offset].dirty = 1'b1; 
                    data_out = '0;
                    end 
                end 
            end 
        end 
    end


    always_comb begin : comb_fsm
        next_state = curr_state; 
        internal_mshr = internal_mshr; 
        load             = 1'b0;
        store            = 1'b0;
        store_data       = '0;
        
        internal_load    = internal_load;
        internal_store   = internal_store;
        internal_store_data = internal_store_data;

        case (curr_state) 
            START: begin 
                if (instr_valid && mshr_entry.valid) begin
                    internal_mshr = mshr_entry; 
                    next_state = BLOCK_PULL;
                end else internal_mshr = mshr_reg'('0); 
            end 
            BLOCK_PULL: begin 
                if (victim_way && (count_BLOCK_PULL == BLOCK_SIZE - 1)) begin 
                    next_state = VICTIM_EJECT; 
                end 
            end 
            VICTIM_EJECT: begin 
                if (count_victim_eject == BLOCK_SIZE - 1) begin 
                    next_state = VICTIM_EJECT; 
                end 
            end 
            FINISH: begin 
                next_state = START; 
            end 
            default: curr_state = START;  
        endcase
    end 


endmodule