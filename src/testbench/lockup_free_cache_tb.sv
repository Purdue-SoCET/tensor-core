`timescale 1ps/1ps

`include "cache_types_pkg.svh";

module RAM (
    input logic CLK, nRST,
    input logic [31:0] ram_addr,
    input logic [31:0] ram_store,
    input logic ram_REN, ram_WEN, ram_END,
    output logic [31:0] ram_load,
    output logic ram_ready
);

    localparam cycle_delay = 100;


    logic [31:0] ram_data [logic [31:0]];
    logic [31:0] current_addr, prev_addr;
    logic [31:0] counter, next_counter;
    typedef enum logic [5:0] { start, ram_read, ram_write } state_t;
    state_t state, next_state;
    logic read, write;

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
        read = 0;
        write = 0;
        ram_ready = 0;
        ram_load = 0;

        case (state)
            start: begin
            end
            ram_read: begin
                if (!ram_REN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    read = 1;
                    ram_ready = 1;     
                    ram_load = ram_data[current_addr];               
                end else begin
                    next_counter = counter + 1;
                end
            end
            ram_write: begin
                if (!ram_WEN || current_addr != prev_addr) begin
                    next_counter = 0;
                end else if (counter == cycle_delay) begin
                    write = 1;
                    ram_ready = 1;
                    ram_data[current_addr] = ram_store;
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
    logic [31:0] tb_ram_addr;
    logic [31:0] tb_ram_load;
    logic [31:0] tb_ram_store;
    logic tb_ram_REN, tb_ram_WEN, tb_ram_ready;
    logic tb_ram_END;

    RAM u_RAM (
        .CLK (tb_clk),
        .nRST (tb_nrst),
        .ram_addr     (tb_ram_addr),
        .ram_store    (tb_ram_store),
        .ram_REN      (tb_ram_REN),
        .ram_WEN      (tb_ram_WEN),
        .ram_load     (tb_ram_load),
        .ram_ready    (tb_ram_ready),
        .ram_END (tb_ram_END)
    );

    always begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2.0);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2.0);
    end

    initial begin
        tb_nrst = 0;
        tb_ram_addr = 32'h0;
        tb_ram_store = 32'h0;
        tb_ram_REN = 0;
        tb_ram_WEN = 0;
        tb_ram_END = 0;

        @(negedge tb_clk);
        tb_nrst = 1;

        @(posedge tb_clk);
        tb_ram_addr = 32'h4567;
        tb_ram_store = 32'h5678;
        tb_ram_WEN = 1;
        while (tb_ram_ready == 0) begin
            @(posedge tb_clk);
        end
        tb_ram_WEN = 0;
        tb_ram_REN = 1;
        @(posedge tb_clk);
        while (tb_ram_ready == 0) begin
            @(posedge tb_clk);
        end
        $display("%08x:%08x", tb_ram_addr, tb_ram_load);
        tb_ram_REN = 0;
        $finish;
    end


endmodule