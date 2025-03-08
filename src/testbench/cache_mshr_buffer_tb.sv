`timescale 1ps/1ps

`include "cache_types_pkg.svh";

module cache_mshr_buffer_tb ();
    localparam CLK_PERIOD = 1;

    logic tb_clk;
    logic tb_nrst;
    logic tb_miss;
    in_mem_instr tb_mem_instr;
    logic tb_bank_empty;
    mshr_reg tb_mshr_out;
    logic tb_stall;
    logic [UUID_SIZE-1:0] tb_mem_out_uuid;

    always begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2.0);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2.0);
    end



    parameter MSHR_BUFFER_LEN = 4;
    cache_mshr_buffer buffer (.CLK(tb_clk), .nRST(tb_nrst), .miss(tb_miss), .mem_instr(tb_mem_instr), .bank_empty(tb_bank_empty), .uuid_out(tb_mem_out_uuid), .mshr_out(tb_mshr_out), .stall(tb_stall));
    test PROG (tb_clk, tb_nrst, tb_miss, tb_mem_instr, tb_bank_empty, tb_mem_out_uuid, tb_mshr_out, tb_stall);

    bind cache_mshr_buffer confirm_uuid uuid_monitor (
        .CLK(CLK), 
        .nRST(nRST),
        .miss(miss), 
        .uuid_out(uuid_out),
        .uuid(uuid)
    );

endmodule

program test (input logic tb_clk,
            output logic tb_nrst,
            output logic tb_miss,
            output in_mem_instr tb_mem_instr,
            output logic tb_bank_empty,
            input [UUID_SIZE-1:0] tb_mem_out_uuid, 
            input mshr_reg tb_mshr_out,
            input logic tb_stall);
    initial begin
        // Full reset
        tb_nrst = 0;
        tb_miss = 0;
        tb_mem_instr = {addr_t'(32'd0), 1'b0, 32'd0};
        tb_bank_empty = 1'b0;
        @(posedge tb_clk);
        @(posedge tb_clk);

        // Send miss
        tb_nrst = 1;
        tb_miss = 1;
        tb_mem_instr = {addr_t'(32'h4567), 1'b0, 32'd4};
        tb_bank_empty = 1'b1;
        @(posedge tb_clk);
        tb_miss = 0;
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);
        @(posedge tb_clk);

        $info("finished!");
    end
endprogram

