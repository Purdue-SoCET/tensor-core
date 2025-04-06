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
                    $display("RAM -- read from %08x: %08x", current_addr, ram_load);     
                end else begin
                    next_counter = counter + 1;
                end
            end
            ram_write: begin
                if (!ram_WEN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    ram_ready = 1;
                    ram_data[current_addr] = ram_store;
                    $display("RAM -- write to %08x: %08x", current_addr, ram_store);
                end else begin
                    next_counter = counter + 1;
                end
            end   
        endcase
    end


endmodule


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
    logic [3:0] tb_mem_in_uuid;
    logic [31:0] tb_mem_in_addr;
    logic tb_mem_in_rw_mode;
    logic [31:0] tb_mem_in_store_value;
    logic tb_stall;
    logic tb_hit;
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
        .mem_in_uuid           (tb_mem_in_uuid),
        .mem_in_addr           (tb_mem_in_addr),
        .mem_in_rw_mode        (tb_mem_in_rw_mode),
        // 0 = read, 1 = writetb_
        .mem_in_store_value    (tb_mem_in_store_value),
        .stall                 (tb_stall),
        .hit                   (tb_hit),
        .hit_load              (tb_hit_load),
        .block_status          (tb_block_status),
        .uuid_block            (tb_uuid_block),
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
                .ram_ready    (tb_ram_mem_complete[i])
            );
        end
    endgenerate

    task data_read(input logic [31:0] addr, input logic [3:0] uuid, output logic [31:0] data);
        @(posedge tb_clk);
        tb_mem_in = 1;
        tb_mem_in_uuid = uuid;
        tb_mem_in_addr = addr;
        tb_mem_in_rw_mode = 0;
        tb_mem_in_store_value = 0;
        @(negedge tb_clk);
        if (!tb_hit) begin
            $display("miss!");
            @(posedge tb_clk);
            tb_mem_in = 0;
            tb_mem_in_uuid = uuid;
            tb_mem_in_addr = addr;
            tb_mem_in_rw_mode = 0;
            @(negedge tb_clk);
            while (tb_block_status == 0) begin
                @(posedge tb_clk);
            end
            $display("block status: %b", tb_block_status);
            @(posedge tb_clk);
        end else begin
            $display("read hit on %08x: %08x!", addr, tb_hit_load);
            data = tb_hit_load;
        end
    endtask

    task data_write(input logic [31:0] addr, input logic [3:0] uuid, input logic [31:0] data);
        @(posedge tb_clk);
        tb_mem_in = 1;
        tb_mem_in_uuid = uuid;
        tb_mem_in_addr = addr;
        tb_mem_in_rw_mode = 1;
        tb_mem_in_store_value = data;
    endtask


    logic [31:0] data_out;

    initial begin
        tb_nrst = 0;
        tb_mem_in = 0;
        tb_mem_in_uuid = 0;
        tb_mem_in_addr = 0;
        tb_mem_in_rw_mode = 0;
        tb_mem_in_store_value = 0;
        @(negedge tb_clk);
        tb_nrst = 1;
        @(posedge tb_clk);
        $display("starting!");
        data_write(32'h4560, 4'd5, 32'h5678);
        data_write(32'h4564, 4'd5, 32'h6789);
        while (tb_block_status == 0) begin
            @(posedge tb_clk);
        end
        tb_mem_in = 0;
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        data_read(32'h4560, 4'd6, data_out);
        $finish;
    end

endmodule