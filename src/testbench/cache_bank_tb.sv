`timescale 1ps/1ps
`include "cache_types_pkg.svh";

module RAM (
    input logic CLK, nRST,
    input logic [31:0] ram_addr,
    input logic [31:0] ram_store,
    input logic ram_REN, ram_WEN,
    output logic [31:0] ram_load,
    output logic ram_ready
);

    localparam cycle_delay = 5;

    logic [31:0] next_ram_data [logic [31:0]];
    logic [31:0] ram_data [logic [31:0]];
    logic [31:0] current_addr, prev_addr;
    logic [31:0] counter, next_counter;
    typedef enum logic [5:0] { start, ram_read, ram_write } state_t;
    state_t state, next_state;

    assign current_addr = ram_addr;

    always_ff @ (posedge CLK, negedge nRST) begin
        if (!nRST) begin
            counter <= 0;
            state <= start;
            prev_addr <= 0;
            ram_data <= '{default: '{default: 0}}; 
        end else begin
            counter <= next_counter;
            state <= next_state;
            prev_addr <= current_addr;
            ram_data <= next_ram_data; 
        end
    end

    always_comb begin
        next_state = state;

        case (state)
            start: begin
                if (ram_REN) begin
                    next_state = ram_read;
                end
                if (ram_WEN) begin
                    next_state = ram_write;
                end
            end
            ram_read: begin
                if (!ram_REN) begin
                    next_state = ram_WEN ? ram_write : start;
                end
                if (current_addr != prev_addr) begin
                    next_state = ram_WEN ? ram_write : (ram_REN ? ram_read : start);
                end
            end
            ram_write: begin
                if (!ram_WEN) begin
                    next_state = ram_REN ? ram_read : start;
                end
                if (current_addr != prev_addr) begin
                    next_state = ram_WEN ? ram_write : (ram_REN ? ram_read : start);
                end
            end
        endcase
    end

    always_comb begin
        next_counter = counter;
        ram_ready = 0;
        ram_load = 0;
        next_ram_data = ram_data;

        case (state)
            start: begin
            end
            ram_read: begin
                if (!ram_REN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    ram_ready = 1;
                    ram_load = ram_data[current_addr];               
                    $display("read from %08x: %08x", current_addr, ram_load);     
                end else begin
                    next_counter = counter + 1;
                end
            end
            ram_write: begin
                if (!ram_WEN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    ram_ready = 1;
                    next_ram_data[current_addr] = ram_store;
                    $display("write %08x: %08x", current_addr, ram_store);     
                end else begin
                    next_counter = counter + 1;
                end
            end   
        endcase
    end


endmodule


module cache_bank_tb;
    localparam CLK_PERIOD = 10; 
    localparam int MAX_INIT_ADDR = 256;

    logic tb_clk;
    logic tb_nrst;
    logic [BANKS_LEN-1:0] tb_bank_id;
    logic tb_instr_valid;
    logic [CACHE_RW_SIZE-1:0] tb_ram_mem_data;
    mshr_reg tb_mshr_entry;
    in_mem_instr tb_mem_instr;
    logic tb_ram_mem_complete;
    logic tb_cache_bank_busy;
    logic tb_scheduler_hit;
    logic tb_ram_mem_REN;
    logic tb_ram_mem_WEN;
    logic [CACHE_RW_SIZE-1:0] tb_ram_mem_store;
    addr_t tb_ram_mem_addr;
    logic [31:0] tb_scheduler_data_out;
    logic [3:0] tb_scheduler_uuid_out;
    logic tb_scheduler_uuid_ready; 
    logic [31:0] zero_val = 32'd0;

    always begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2);
    end


    initial begin 
        // u_RAM.ram_data = 
        $dumpfile("waveforms/cache_bank_tb.vcd");
        $dumpvars(0);
    end 
    
    RAM u_RAM (
        .CLK(tb_clk),
        .nRST(tb_nrst),
        .ram_addr(tb_ram_mem_addr),
        .ram_store(tb_ram_mem_store),
        .ram_REN(tb_ram_mem_REN),
        .ram_WEN (tb_ram_mem_WEN),
        .ram_load(tb_ram_mem_data),
        .ram_ready(tb_ram_mem_complete)
    );


    // genvar addr;
    // generate
    // for (addr = 0; addr < MAX_INIT_ADDR; addr = addr + 1) begin : force_ram_data
    //     initial begin
    //         @(posedge tb_nrst);
    //         force u_RAM.ram_data[addr] = zero_val;
    //     end
    // end
    // endgenerate

    cache_bank dut (
        .CLK(tb_clk),
        .nRST(tb_nrst),
        .bank_id(tb_bank_id),
        .instr_valid(tb_instr_valid),
        .ram_mem_data(tb_ram_mem_data),
        .mshr_entry(tb_mshr_entry),
        .mem_instr_in(tb_mem_instr),
        .ram_mem_complete(tb_ram_mem_complete),
        .cache_bank_busy(tb_cache_bank_busy),
        .scheduler_hit(tb_scheduler_hit),
        .ram_mem_REN(tb_ram_mem_REN),
        .ram_mem_WEN(tb_ram_mem_WEN),
        .ram_mem_store(tb_ram_mem_store),
        .ram_mem_addr(tb_ram_mem_addr),
        .scheduler_data_out(tb_scheduler_data_out),
        .scheduler_uuid_out(tb_scheduler_uuid_out),
        .scheduler_uuid_ready(tb_scheduler_uuid_ready)
    );


    bind cache_bank confirm_lru_age lru_monitor (
        .CLK(CLK), 
        .nRST(nRST), 
        .curr_state(curr_state),
        .lru(lru),
        .latched_victim_set_index(latched_victim_set_index),
        .latched_victim_way_index(latched_victim_way_index)
    );

    bind cache_bank confirm_replacement_mshr mshr_monitor (
        .CLK(CLK), 
        .nRST(nRST), 
        .curr_state(curr_state), 
        .latched_victim_set_index(latched_victim_set_index),
        .latched_victim_way_index(latched_victim_way_index),
        .bank(bank), 
        .mshr_entry(mshr_entry), 
        .count_FSM(count_FSM),
        .latched_block_pull_buffer(latched_block_pull_buffer)
    );

    bind cache_bank confirm_replacement_singlecycle singlecycle_monitor (
        .CLK(CLK), 
        .nRST(nRST), 
        .mem_instr_in(mem_instr_in),
        .scheduler_hit(scheduler_hit), 
        .set_index(set_index), 
        .hit_way_index(hit_way_index),
        .bank(bank)
    );

    test PROG (
        .tb_clk(tb_clk),
        .tb_nrst(tb_nrst),
        .tb_bank_id(tb_bank_id),
        .tb_instr_valid(tb_instr_valid),
        .tb_ram_mem_data(tb_ram_mem_data),
        .tb_mshr_entry(tb_mshr_entry),
        .tb_mem_instr(tb_mem_instr),
        .tb_ram_mem_complete(tb_ram_mem_complete),
        .tb_cache_bank_busy(tb_cache_bank_busy),
        .tb_scheduler_hit(tb_scheduler_hit),
        .tb_ram_mem_REN(tb_ram_mem_REN),
        .tb_ram_mem_WEN(tb_ram_mem_WEN),
        .tb_ram_mem_store(tb_ram_mem_store),
        .tb_ram_mem_addr(tb_ram_mem_addr),
        .tb_scheduler_data_out(tb_scheduler_data_out),
        .tb_scheduler_uuid_out(tb_scheduler_uuid_out), 
        .tb_scheduler_uuid_ready(tb_scheduler_uuid_ready)
    );

endmodule

// Calculated Cache Parameters:
// -------------------------------
// CACHE_SIZE         = 1024
// BLOCK_SIZE         = 4
// NUM_WAYS           = 4
// NUM_BANKS          = 4
// MSHR_BUFFER_LEN    = 8
// CACHE_RW_SIZE      = 32

// NUM_SETS           = 16
// NUM_SETS_PER_BANK  = 4
// BYTE_OFF_BIT_LEN   = 2
// BLOCK_OFF_BIT_LEN  = 2
// BLOCK_INDEX_BIT_LEN= 4
// WAYS_LEN           = 2
// BANKS_LEN          = 2
// TAG_BIT_LEN        = 24

program test (
    input logic  tb_clk,
    output logic  tb_nrst,
    output logic [BANKS_LEN-1:0] tb_bank_id,
    output logic  tb_instr_valid,
    output mshr_reg  tb_mshr_entry,
    output in_mem_instr  tb_mem_instr,
    input logic [CACHE_RW_SIZE-1:0] tb_ram_mem_data,
    input logic  tb_ram_mem_complete,
    input logic  tb_cache_bank_busy,
    input logic  tb_ram_mem_REN,
    input logic  tb_ram_mem_WEN,
    input logic [CACHE_RW_SIZE-1:0] tb_ram_mem_store,
    input addr_t  tb_ram_mem_addr,
    input logic [31:0] tb_scheduler_data_out,
    input logic [3:0] tb_scheduler_uuid_out,
    input logic  tb_scheduler_hit,
    input logic  tb_scheduler_uuid_ready
);

    addr_t address;
    mshr_reg tmp_mshr;
    string test_id; 
    logic SingleCycle_RW_Done, MSHR_Thread_Done;
    integer display_bit = 0; 

    task automatic initiate_read_write(
        logic [TAG_BIT_LEN-1:0] tag,
        logic [BLOCK_INDEX_BIT_LEN-1:0] index,
        logic [BLOCK_OFF_BIT_LEN-1:0] block_offset,
        logic [BYTE_OFF_BIT_LEN-1:0] byte_offset,
        logic rw_mode,
        logic [31:0] store_value
    ); 
        tb_instr_valid = 1;
        address = addr_t'{ tag, index, block_offset, byte_offset }; 
        tb_mem_instr  = in_mem_instr'{ address, rw_mode, store_value };
        @(posedge tb_clk);
        tb_instr_valid = 0;
        log_ram_inputs(1, tb_ram_mem_complete, tb_ram_mem_addr, tb_ram_mem_store, tb_ram_mem_WEN, tb_ram_mem_REN, tb_cache_bank_busy, tb_scheduler_data_out, tb_scheduler_uuid_out, tb_scheduler_hit, tb_scheduler_uuid_ready);
        @(posedge tb_clk);
    endtask

    task automatic set_mshr(
        mshr_reg _tb_mshr_entry
    );
        tb_mshr_entry = _tb_mshr_entry;
        @(posedge tb_clk);
    endtask

    task automatic log_ram_inputs(
        integer cycles, 
        logic _tb_ram_mem_complete,
        logic [31:0] _tb_ram_mem_addr,
        logic [CACHE_RW_SIZE-1:0] _tb_ram_mem_store,
        logic _tb_ram_mem_WEN,
        logic _tb_ram_mem_REN,
        logic _tb_cache_bank_busy, 
        logic [31:0] _tb_scheduler_data_out,
        logic [3:0] _tb_scheduler_uuid_out,
        logic  _tb_scheduler_hit, 
        logic _tb_scheduler_uuid_ready
    );
        for (integer i = 0; i < cycles; i++) begin 
            if (display_bit) $display("--> ram_mem_complete: %b, ram_mem_addr: %h, ram_mem_store: %h, ram_mem_WEN: %b, ram_mem_REN: %b, tb_cache_bank_busy: %b", _tb_ram_mem_complete, _tb_ram_mem_addr, _tb_ram_mem_store, _tb_ram_mem_WEN, _tb_ram_mem_REN, _tb_cache_bank_busy);
            if (display_bit) $display("      tb_scheduler_data_out: %d, tb_scheduler_uuid_out: %h, tb_scheduler_hit: %b, _tb_scheduler_uuid_ready: %b", _tb_scheduler_data_out, _tb_scheduler_uuid_out, _tb_scheduler_hit, _tb_scheduler_uuid_ready);
            @(posedge tb_clk);
        end 
    endtask

    task automatic reset();
        tb_nrst = 0;
        tb_bank_id = '0;
        tb_instr_valid = 0;
        tb_mshr_entry = '0;
        address = '0; 
        tb_mem_instr  = '0;
        SingleCycle_RW_Done = 1'b0; 
        MSHR_Thread_Done = 1'b0;
        @(posedge tb_clk);
        @(posedge tb_clk);
        tb_nrst = 1;
        tb_bank_id = BANKS_LEN'(4'd3);
        set_test_id("RESET DONE");
        @(posedge tb_clk);
    endtask

    task automatic fill_bank(
        logic random_valid, 
        logic random_dirty
    );
        for (integer set = 0; set < NUM_SETS_PER_BANK; set++) begin
            for (integer way = 0; way < NUM_WAYS; way++) begin
                dut.next_bank[set][way].valid = (random_valid) ? $urandom_range(0, 1) : 1'b1;
                dut.next_bank[set][way].dirty = (random_dirty) ? $urandom_range(0, 1) : 1'b0;
                dut.next_bank[set][way].tag   = '1; 
                for (integer b = 0; b < BLOCK_SIZE; b++) begin
                    dut.next_bank[set][way].block[b] = {
                        $urandom_range(0, 8'hFF), 
                        $urandom_range(0, 8'hFF), 
                        $urandom_range(0, 8'hFF), 
                        $urandom_range(0, 8'hFF)
                    };
                end
            end
        end
        @(posedge tb_clk);
        @(posedge tb_clk);
    endtask

    task automatic set_test_id(
        string test_in
    );
        test_id = test_in;
        $display(test_in);
    endtask

    task stall_for_ram; 
        wait(tb_ram_mem_complete == 1);
        @(posedge tb_clk);
        wait(tb_ram_mem_complete == 1);
        @(posedge tb_clk);
        wait(tb_ram_mem_complete == 1);
        @(posedge tb_clk);
        wait(tb_ram_mem_complete == 1);
        @(posedge tb_clk);
    endtask

    initial begin

        set_test_id("-------> RESET");
        reset();

        // Starting with empty bank!
        set_test_id("-------> Trying a WRITE - MISS");
        initiate_read_write(
            .tag(24'h1000), 
            .index(4'h9), 
            .block_offset(2'b00), 
            .byte_offset(2'b00), 
            .rw_mode(1'b1), 
            .store_value(32'd0)
        );


        set_test_id("-------> Sending in MSHR Entry");
        set_mshr(
            {1'b1, 4'd9, address, BLOCK_SIZE'('0), cache_block'('0)}
        );
        set_test_id("-------> FSM Initiated");
        stall_for_ram();

        set_mshr('0);

        set_test_id("-------> Trying a READ - HIT");
        initiate_read_write(
            .tag(24'h1000), 
            .index(4'h9), 
            .block_offset(2'b00), 
            .byte_offset(2'b00), 
            .rw_mode(1'b0), 
            .store_value(32'd0)
        );

        set_test_id("-------> FILL BANK");

        set_test_id("-------> RANDOMIZED SIMULATION");
        @(posedge tb_clk);


        MSHR_Thread_Done = 1; 
        SingleCycle_RW_Done = 1; 
        @(posedge tb_clk);

        MSHR_Thread_Done = 0; 
        SingleCycle_RW_Done = 0; 
        @(posedge tb_clk);

        
        fork
        begin : mshr_process
            for (int set = 0; set < NUM_SETS; set++) begin
                for (int way = 0; way < NUM_WAYS; way++) begin
                    MSHR_Thread_Done = 0; 

                    tmp_mshr.valid = 1'b1;
                    tmp_mshr.uuid = (set * NUM_WAYS + way) % 16;
                    tmp_mshr.block_addr = addr_t'{ 
                        {TAG_BIT_LEN{1'b1}}, 
                        set[BLOCK_INDEX_BIT_LEN-1:0], 
                        BLOCK_OFF_BIT_LEN'('0),
                        BYTE_OFF_BIT_LEN'('0)
                    };

                    tmp_mshr.write_status = { BLOCK_SIZE{1'b0} };
                    tmp_mshr.write_block  = '0;

                    set_mshr(tmp_mshr);
                    stall_for_ram();
                    set_mshr('0);
                    MSHR_Thread_Done = 1; 

                    @(posedge tb_clk);
                end
            end
        end

        begin : rw_process
            for (int set = 0; set < NUM_SETS; set++) begin
            for (int block_offset = 0; block_offset < BLOCK_SIZE; block_offset++) begin
                SingleCycle_RW_Done = 0; 

                initiate_read_write(
                    1'b1,                
                    set,               
                    block_offset,        
                    1'b0,               
                    1'b0,              
                    CACHE_RW_SIZE'(32'hBEEFDEAD)
                );

                @(posedge tb_clk);
                SingleCycle_RW_Done = 1; 
                @(posedge tb_clk);
            end
            end
        end
        join


        MSHR_Thread_Done = 0; 
        SingleCycle_RW_Done = 0; 
        @(posedge tb_clk);

        set_test_id("-------> FINISH");

        $finish;
    end
endprogram