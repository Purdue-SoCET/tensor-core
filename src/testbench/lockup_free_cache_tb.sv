`timescale 1ps/1ps

`include "cache_types_pkg.svh";

module RAM (
    input logic [31:0] ram_addr,
    input logic [31:0] ram_store,
    input logic ram_REN, ram_WEN, ram_END
    output logic [31:0] ram_load,
    output logic ram_ready
);

    logic [31:0] ram_data [logic [31:0]];
    logic [31:0] current_addr;

    always begin
        fork
        if (ram_REN) begin
            current_addr = ram_addr;
            #100;
            if (ram_data.exists(ram_addr)) begin
                ram_load = ram_data[ram_addr];
            end else begin
                ram_load = 32'h0;
            end
            ram_ready = 1;
            @(ram_addr != current_addr);
        end else if (ram_WEN) begin
            current_addr = ram_addr;
            #100;
            ram_data[ram_addr] = ram_store;
            ram_ready = 1;
            @(ram_addr != current_addr);
        end else begin
            ram_ready = 0;
            current_addr = 0;
        end
        join
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
        .ram_addr     (tb_ram_addr),
        .ram_store    (tb_ram_store),
        .ram_REN      (tb_ram_REN),
        .ram_WEN      (tb_ram_WEN),
        .ram_load     (tb_ram_load),
        .ram_ready    (tb_ram_ready)
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
        while (tb_ram_ready == 0);
        tb_ram_WEN = 0;
        $finish;
    end


endmodule