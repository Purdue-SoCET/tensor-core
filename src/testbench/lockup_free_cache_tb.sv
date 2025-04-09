`timescale 1ps/1ps

`include "cache_types_pkg.svh";

module RAM (
    input logic CLK, nRST,
    input logic [31:0] ram_addr,
    input logic [31:0] ram_store,
    input logic ram_REN, ram_WEN,
    input logic [BANKS_LEN-1:0] bank_id,
    output logic [31:0] ram_load,
    output logic ram_ready
);

    localparam cycle_delay = 5;

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
        end else begin
            counter <= next_counter;
            state <= next_state;
            prev_addr <= current_addr;
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

        case (state)
            start: begin
                if (!ram_WEN && !ram_REN) ram_ready = 1; 
            end
            ram_read: begin
                if (!ram_REN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    ram_ready = 1;
                    if (ram_data.exists(current_addr)) begin
                        ram_load = ram_data[current_addr]; 
                    end else begin
                        ram_load = 32'd0;
                    end            
                    // // $display("RAM ID:%d -- read from %08x: %08x", bank_id, current_addr, ram_load);     
                end else begin
                    next_counter = counter + 1;
                end
            end
            ram_write: begin
                if (!ram_WEN || ram_REN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    ram_ready = 1;
                    ram_data[current_addr] = ram_store;
                    // // $display("RAM ID:%d -- write to %08x: %08x", bank_id, current_addr, ram_store);
                end else begin
                    next_counter = counter + 1;
                end
            end   
        endcase
    end


endmodule

class cache_line;
    logic [BLOCK_INDEX_BIT_LEN-1:0] set_index;
    rand logic [TAG_BIT_LEN-1:0] tag;
    addr_t [BLOCK_SIZE-1:0] addr;
    rand logic [BLOCK_SIZE-1:0][31:0] data;
    rand logic [BLOCK_SIZE-1:0][31:0] data2;
    integer i;

    function new(logic [BLOCK_INDEX_BIT_LEN-1:0] set_index);
        this.set_index = set_index;
        randomize();
        for (i = 0; i < BLOCK_SIZE; i++) begin
            addr[i].tag = tag;
            addr[i].index = set_index;
            addr[i].block_offset = i;
            addr[i].byte_offset = 0;
        end
    endfunction
endclass

module lockup_free_cache_tb;
    localparam CLK_PERIOD = 1;

    logic tb_clk;
    logic tb_nrst;

    always begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2.0);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2.0);
    end

    logic tb_mem_in;
    logic [UUID_SIZE-1:0] tb_mem_out_uuid;
    logic [UUID_SIZE-1:0] uuid;
    logic [31:0] tb_mem_in_addr;
    logic tb_mem_in_rw_mode;
    logic [31:0] tb_mem_in_store_value;
    logic tb_stall;
    logic tb_hit;
    logic tb_halt;
    logic tb_flushed;
    logic [31:0] tb_hit_load;
    logic [NUM_BANKS-1:0] tb_block_status;
    logic [NUM_BANKS-1:0][3:0] tb_uuid_block;
    logic [NUM_BANKS-1:0] tb_ram_mem_REN;
    logic [NUM_BANKS-1:0] tb_ram_mem_WEN;
    logic [NUM_BANKS-1:0][31:0] tb_ram_mem_addr;
    logic [NUM_BANKS-1:0][31:0] tb_ram_mem_store;
    logic [NUM_BANKS-1:0][31:0] tb_ram_mem_data;
    logic [NUM_BANKS-1:0] tb_ram_mem_complete;

    lockup_free_cache u_lockup_free_cache (
        .CLK                   (tb_clk),
        .nRST                  (tb_nrst),
        .mem_in                (tb_mem_in),
        .mem_out_uuid           (tb_mem_out_uuid),
        .mem_in_addr           (tb_mem_in_addr),
        .mem_in_rw_mode        (tb_mem_in_rw_mode),
        // 0 = read, 1 = writetb_
        .mem_in_store_value    (tb_mem_in_store_value),
        .dp_in_halt            (tb_halt),
        .stall                 (tb_stall),
        .hit                   (tb_hit),
        .hit_load              (tb_hit_load),
        .block_status          (tb_block_status),
        .uuid_block            (tb_uuid_block),
        .dp_out_flushed        (tb_flushed),
        // RAM Signalstb_
        .ram_mem_REN           (tb_ram_mem_REN),
        .ram_mem_WEN           (tb_ram_mem_WEN),
        .ram_mem_addr          (tb_ram_mem_addr),
        .ram_mem_store         (tb_ram_mem_store),
        .ram_mem_data          (tb_ram_mem_data),
        .ram_mem_complete      (tb_ram_mem_complete)
    );

    genvar i;
    generate
        for (i = 0; i < NUM_BANKS; i++) begin : RAM_GEN
            RAM u_RAM (
                .CLK          (tb_clk),
                .nRST         (tb_nrst),
                .ram_addr     (tb_ram_mem_addr[i]),
                .ram_store    (tb_ram_mem_store[i]),
                .ram_REN      (tb_ram_mem_REN[i]),
                .ram_WEN      (tb_ram_mem_WEN[i]),
                .ram_load     (tb_ram_mem_data[i]),
                .ram_ready    (tb_ram_mem_complete[i]),
                .bank_id (BANKS_LEN'(i))
            );
        end
    endgenerate

    task data_read(input logic [31:0] addr, output logic [31:0] data);
        // $display("Starting data read: %08x", addr);
        @(posedge tb_clk);
        tb_mem_in = 1;
        tb_mem_in_addr = addr;
        tb_mem_in_rw_mode = 0;
        tb_mem_in_store_value = 0;
        @(negedge tb_clk);
        if (tb_hit) begin
            // $display("Read hit on %08x! -> %08x", addr, tb_hit_load);
            data = tb_hit_load;
        end else begin
            // $display("Read miss on %08x!", addr);
            while (tb_stall) begin
                // $display("Cache stall!");
                @(posedge tb_clk);
                @(negedge tb_clk);
            end
        end
    endtask

    task data_write(input logic [31:0] addr, input logic [31:0] data);
        // $display("Starting data write: %08x,%08x", addr, data);
        @(posedge tb_clk);
        tb_mem_in = 1;
        tb_mem_in_addr = addr;
        tb_mem_in_rw_mode = 1;
        tb_mem_in_store_value = data;
        @(negedge tb_clk);
        if (tb_hit) begin
            // $display("Write hit on %08x!", addr);
        end else begin
            // $display("Write miss on %08x!", addr);
            while (tb_stall) begin
                // $display("Cache stall!");
                @(posedge tb_clk);
                @(negedge tb_clk);
            end
        end
    endtask

    task cycle_wait(input integer cycle_count);
        for (cycle_count = 0; cycle_count < 100000; cycle_count++) begin
            @(posedge tb_clk);
        end
    endtask


    logic [31:0] data_out;
    string testcase; 

    integer current_set_index;
    integer current_block_offset;
    integer current_way;

    cache_line line [3:0];

    localparam test_set_num = 4;

    initial begin
        tb_nrst = 0;
        tb_mem_in = 0;
        tb_mem_in_addr = 0;
        tb_mem_in_rw_mode = 0;
        tb_mem_in_store_value = 0;
        @(negedge tb_clk);
        tb_nrst = 1;
        testcase = "PART 1";
        @(posedge tb_clk);        
        for (current_way = 0; current_way < NUM_WAYS; current_way++) begin
            for (current_set_index = 0; current_set_index < test_set_num; current_set_index++) begin
                line[current_set_index] = new(current_set_index);

                if (current_way % 2 == 0) begin
                    // Write miss
                    for (current_block_offset = 0; current_block_offset < 1; current_block_offset++) begin
                        data_write(line[current_set_index].addr[current_block_offset], 32'h88888888);                
                    end
                end else begin
                    // Read miss
                    for (current_block_offset = 0; current_block_offset < 1; current_block_offset++) begin
                        data_read(line[current_set_index].addr[current_block_offset], data_out);                
                    end
                end
            end
            @(posedge tb_clk);
            tb_mem_in = 0;
            @(negedge tb_clk);
            while (tb_block_status[NUM_BANKS-1] == 0) begin
                @(posedge tb_clk);
                @(negedge tb_clk);
                // $display("Waiting for misses to finish!");
            end
            for (current_set_index = 0; current_set_index < test_set_num; current_set_index++) begin
                // Write hit
                for (current_block_offset = 0; current_block_offset < BLOCK_SIZE; current_block_offset++) begin
                    data_write(line[current_set_index].addr[current_block_offset], line[current_set_index].data[current_block_offset]);
                end
                // Read hit
                for (current_block_offset = 0; current_block_offset < BLOCK_SIZE; current_block_offset++) begin
                    data_read(line[current_set_index].addr[current_block_offset], data_out);
                end
            end
        end
        @(posedge tb_clk);
        tb_mem_in = 0;
        testcase = "PART 2";
        @(posedge tb_clk);
        for (current_way = 0; current_way < NUM_WAYS; current_way++) begin
            for (current_set_index = 0; current_set_index < test_set_num; current_set_index++) begin
                line[current_set_index] = new(current_set_index);
                for (current_block_offset = 0; current_block_offset < BLOCK_SIZE; current_block_offset++) begin
                    // Read miss
                    data_read(line[current_set_index].addr[current_block_offset], data_out);
                end
                for (current_block_offset = 0; current_block_offset < BLOCK_SIZE; current_block_offset++) begin
                    // Write miss coalescing
                    data_write(line[current_set_index].addr[current_block_offset], line[current_set_index].data[current_block_offset]);
                end
                cycle_wait(1);
                for (current_block_offset = 0; current_block_offset < BLOCK_SIZE; current_block_offset++) begin
                    // Read mshr (miss->hit) coalescing
                    data_read(line[current_set_index].addr[current_block_offset], data_out);
                end
            end
            @(posedge tb_clk);
            tb_mem_in = 0;
            cycle_wait(4 * 100);
        end
        $finish;
    end

endmodule