`timescale 1ps/1ps
`include "cache_types_pkg.svh";

module cache_bank_tb;
    localparam CLK_PERIOD = 10; 

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
    logic [31:0] tb_ram_mem_addr;
    logic [31:0] tb_scheduler_data_out;
    logic [3:0] tb_scheduler_uuid_out;

    always begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2);
    end

    initial begin 
        $dumpfile("waveforms/cache_bank_tb.vcd");
        $dumpvars(0, cache_bank_tb);
    end 
    
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
        .scheduler_uuid_out(tb_scheduler_uuid_out)
    );

    bind cache_bank confirm_lru_age lru_mon_inst (
        .CLK(CLK), 
        .lru(lru)
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
        .tb_scheduler_uuid_out(tb_scheduler_uuid_out)
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
    output logic [CACHE_RW_SIZE-1:0] tb_ram_mem_data,
    output mshr_reg  tb_mshr_entry,
    output in_mem_instr  tb_mem_instr,
    output logic  tb_ram_mem_complete,
    input logic  tb_cache_bank_busy,
    input logic  tb_ram_mem_REN,
    input logic  tb_ram_mem_WEN,
    input logic [CACHE_RW_SIZE-1:0] tb_ram_mem_store,
    input logic [31:0] tb_ram_mem_addr,
    input logic [31:0] tb_scheduler_data_out,
    input logic [3:0] tb_scheduler_uuid_out,
    input logic  tb_scheduler_hit
);

    addr_t address;
    string test; 

    task automatic initiate_read_write(
        logic [TAG_BIT_LEN-1:0] tag,
        logic [BLOCK_INDEX_BIT_LEN-1:0] index,
        logic [BLOCK_OFF_BIT_LEN-1:0] block_offset,
        logic [BYTE_OFF_BIT_LEN-1:0] byte_offset,
        logic [3:0] uuid,
        logic rw_mode,
        logic [31:0] store_value
    ); 
        tb_instr_valid = 1;
        address = { tag, index, block_offset, byte_offset }; 
        tb_mem_instr  = {uuid, address, rw_mode, store_value };
        @(posedge tb_clk);
        tb_instr_valid = 0;
        log_ram_inputs(1, tb_ram_mem_complete, tb_ram_mem_addr, tb_ram_mem_store, tb_ram_mem_WEN, tb_ram_mem_REN, tb_cache_bank_busy, tb_scheduler_data_out, tb_scheduler_uuid_out, tb_scheduler_hit);
    endtask

    task automatic set_mshr(
        mshr_reg _tb_mshr_entry,
        logic [CACHE_RW_SIZE-1:0] _tb_ram_mem_data,
        logic _tb_ram_mem_complete
    );
        tb_mshr_entry = _tb_mshr_entry;
        tb_ram_mem_data = _tb_ram_mem_data;
        tb_ram_mem_complete = _tb_ram_mem_complete;
        @(posedge tb_clk);
    endtask

    task automatic initiate_fsm();
        $display("Completed START, should begin BLOCK_PULL now");
        log_ram_inputs(4, tb_ram_mem_complete, tb_ram_mem_addr, tb_ram_mem_store, tb_ram_mem_WEN, tb_ram_mem_REN, tb_cache_bank_busy, tb_scheduler_data_out, tb_scheduler_uuid_out, tb_scheduler_hit);

        $display("Completed BLOCK_PULL, should begin VICTIM_EJECT now");
        log_ram_inputs(4, tb_ram_mem_complete, tb_ram_mem_addr, tb_ram_mem_store, tb_ram_mem_WEN, tb_ram_mem_REN, tb_cache_bank_busy, tb_scheduler_data_out, tb_scheduler_uuid_out, tb_scheduler_hit);
        tb_ram_mem_complete = 1'b0; 

        $display("Completed VICTIM_EJECT, should begin FINISH now");
        log_ram_inputs(1, tb_ram_mem_complete, tb_ram_mem_addr, tb_ram_mem_store, tb_ram_mem_WEN, tb_ram_mem_REN, tb_cache_bank_busy, tb_scheduler_data_out, tb_scheduler_uuid_out, tb_scheduler_hit);
    endtask

    task automatic log_ram_inputs(
        int cycles, 
        logic _tb_ram_mem_complete,
        logic [31:0] _tb_ram_mem_addr,
        logic [CACHE_RW_SIZE-1:0] _tb_ram_mem_store,
        logic _tb_ram_mem_WEN,
        logic _tb_ram_mem_REN,
        logic _tb_cache_bank_busy, 
        logic [31:0] _tb_scheduler_data_out,
        logic [3:0] _tb_scheduler_uuid_out,
        logic  _tb_scheduler_hit 
    );

        for (int i = 0; i < cycles; i++) begin 
            $display("  --> ram_mem_complete: %b, ram_mem_addr: %h, ram_mem_store: %h, ram_mem_WEN: %b, ram_mem_REN: %b, tb_cache_bank_busy: %b", _tb_ram_mem_complete, _tb_ram_mem_addr, _tb_ram_mem_store, _tb_ram_mem_WEN, _tb_ram_mem_REN, _tb_cache_bank_busy);
            $display("      tb_scheduler_data_out: %d, tb_scheduler_uuid_out: %h, tb_scheduler_hit: %b", _tb_scheduler_data_out, _tb_scheduler_uuid_out, _tb_scheduler_hit);
            @(posedge tb_clk);
        end 
    endtask

    task automatic reset();
        tb_nrst = 0;
        tb_bank_id = '0;
        tb_instr_valid = 0;
        tb_ram_mem_data = '0;
        tb_mshr_entry = '0;
        tb_ram_mem_complete = 0;
        @(posedge tb_clk);
        @(posedge tb_clk);
        tb_nrst = 1;
        tb_bank_id = BANKS_LEN'(4'd3);
        @(posedge tb_clk);
    endtask

    initial begin

        
        reset();
        
        $display("-------> Trying a READ - MISS");
        initiate_read_write(
            .tag(24'd10245), 
            .index(4'd15), 
            .block_offset(2'b00), 
            .byte_offset(2'b00), 
            .uuid(4'd9), 
            .rw_mode(1'b0), 
            .store_value(32'd0)
        );

        $display("-------> Sending in MSHR Entry");
        set_mshr(
            {1'b1, 4'd9, address, BLOCK_SIZE'('0), cache_block'(0)}, 
            CACHE_RW_SIZE'(32'd2048), 
            1'b1
        );

        $display("-------> FSM Initiated");
        initiate_fsm();

        $display("-------> Removing MSHR Entry");
        set_mshr(
            '0, 
            '0, 
            1'b0
        );

        $display("-------> Trying a READ - HIT");
        initiate_read_write(
            .tag(24'd10245), 
            .index(4'd15), 
            .block_offset(2'b00), 
            .byte_offset(2'b00), 
            .uuid(4'd9), 
            .rw_mode(1'b0), 
            .store_value(32'd0)
        );

        $finish;
    end
endprogram