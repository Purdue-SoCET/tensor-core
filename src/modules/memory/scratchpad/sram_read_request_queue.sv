`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "sram_read_req_queue_if.vh"

    // modport baceknd_sram_read_req_queue ( 
    //     input xbar_desc, id, be_dr_r_req_accepted,
    //     input sched_write
    //     input be_sram_rd_req_accepted,

    //     output sram_read_req, sram_read_queue_full, sram_read_req_latched
    // );

module sram_read_request_queue (
    input logic clk, n_rst, 
    sram_read_req_queue.baceknd_dram_read_req_queue be_sr_rd_req_q
);
    import scpad_types_pkg::*;

    // typedef struct packed {
    //         logic        valid;     
    //         logic        row_or_col;        
    //         xbar_desc_t  xbar;
    // } sram_read_req_t;

    sram_read_req_t [DRAM_ID_WIDTH-1:0] sram_rd_req_latch_block; // 32 frames
    sram_read_req_t nxt_sram_head_latch_set, nxt_sram_tail_latch_set;

    logic [DRAM_ID_WIDTH-1:0] fifo_head, nxt_fifo_head, fifo_tail, nxt_fifo_tail;
    
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            sram_rd_req_latch_block <= 'b0;
            fifo_head <= 'b0;
            fifo_tail <= 'b0;
        end else begin
            sram_rd_req_latch_block[fifo_head] <= nxt_sram_head_latch_set;
            sram_rd_req_latch_block[fifo_tail] <= nxt_sram_tail_latch_set;
            fifo_head <= nxt_fifo_head;
            fifo_tail <= nxt_fifo_tail
        end
    end

    always_comb begin
        nxt_sram_head_latch_set = sram_rd_req_latch_block[fifo_head];
        nxt_sram_tail_latch_set = sram_rd_req_latch_block[fifo_tail];
        nxt_fifo_head = fifo_head;
        nxt_fifo_tail = fifo_tail;
        sram_read_req_latched = 1'b0;
        be_sr_rd_req_q.sram_read_queue_full = 1'b0;

        if(be_sr_rd_req_q.sched_write == 1'b0) begin
            nxt_sram_tail_latch_set.valid = 1'b1;
            nxt_sram_tail_latch_set.row_or_col = be_sr_rd_req_q.row_or_col;
            nxt_sram_tail_latch_set.xbar = be_sr_rd_req_q.xbar;
            nxt_fifo_tail = fifo_tail + 1;
            be_sr_rd_req_q.sram_read_req_latched = 1'b1;
        end

        if(be_sr_rd_req_q.be_sram_rd_req_accepted) begin
            nxt_sram_head_latch_set = 0; // invalidate head when our request are accepted.
            nxt_fifo_head = fifo_head + 1;
        end

        if((fifo_tail + 1) == fifo_head) begin 
            nxt_sram_tail_latch_set = sram_rd_req_latch_block[fifo_tail];
            nxt_fifo_tail = fifo_tail;
            be_sr_rd_req_q.sram_read_req_latched = 1'b0;
            be_sr_rd_req_q.sram_read_queue_full = 1'b1;
        end

    be_sr_rd_req_q.sram_read_req = sram_rd_req_latch_block[fifo_head];

    end
    

endmodule
