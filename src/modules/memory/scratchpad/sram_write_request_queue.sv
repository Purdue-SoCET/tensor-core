`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "sram_write_req_queue_if.vh"

    // modport baceknd_sram_write_req_queue ( 
    //     input  xbar, dram_data_id, dr_rdata, be_sram_wr_req_accepted,
    //     input be_dr_wr_req_complete,

    //     output sram_write_req, sram_write_queue_full, sram_write_req_latched
    // );

module sram_write_request_queue (
    input logic clk, n_rst, 
    sram_write_req_queue.baceknd_sram_write_req_queue be_sr_wr_req_q
);
    import scpad_types_pkg::*;

    // typedef struct packed {
    //         logic       valid;     
    //         logic       row_or_col;        
    //         xbar_desc_t  xbar;  
    //         scpad_data_t wdata;
    // } sram_write_req_t;

    sram_write_req_t [DRAM_ID_WIDTH-1:0] sram_wr_req_latch_block; // 32 latch sets for our queue
    sram_write_req_t nxt_sram_latch_set;

    logic [DRAM_ID_WIDTH-1:0][DRAM_ID_WIDTH-1:0] req_queue;
    logic [DRAM_ID_WIDTH-1:0] nxt_req_queue, queue_head, nxt_queue_head, queue_tail, nxt_queue_tail; 
    // The request queue will keep track of what the current latch to send out should be
    // There are 32 latches so need to track of an array of size 32 with the elements being ints that go up to 32.
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            sram_wr_req_latch_block <= 'b0;
            req_queue  <= 'b0;
            queue_head <= 'b0;
            queue_tail <= 'b0;
        end else begin
            sram_wr_req_latch_block[be_sr_wr_req_q.dram_data_id] <= nxt_sram_latch_set;
            req_queue[queue_head]  <= nxt_req_queue; 
            queue_head <= nxt_queue_head;
            queue_tail <= nxt_queue_tail;                            
        end
    end

    always_comb begin
        be_sr_wr_req_q.sram_write_req = 0;
        nxt_sram_latch_set = sram_wr_req_latch_block[be_sr_wr_req_q.dram_data_id];
        nxt_req_queue = req_queue;
        nxt_queue_head = queue_head;
        nxt_queue_tail = queue_tail;
        sram_write_req_latched = 1'b0;
        be_sr_wr_req_q.sram_write_queue_full = 1'b0; 

        if(be_sr_wr_req_q.be_dr_rd_req_complete) begin
            nxt_sram_latch_set.valid = 1'b1;
            nxt_sram_latch_set.row_or_col = be_sr_wr_req_q.row_or_col;
            nxt_sram_latch_set.xbar = be_sr_wr_req_q.xbar;
            nxt_sram_latch_set.wdata = be_sr_wr_req_q.dr_rdata;
            nxt_req_queue = be_sr_wr_req_q.dram_data_id; 
            // This is what seperates it from dram_r_req. In the request queue's head store the dram_data_id we got from dram
            // Then our output will be based on that head and they can be queued up.
            nxt_queue_tail = queue_tail + 1;
            be_sr_wr_req_q.sram_write_req_latched = 1'b1;
        end
        // This is if the whole packet came back at once (it doesn't). Will need to discuss how that looks with DRAM
        // Most likely an fsm but it's possible a request is less than 4 packets so can't just say when we see the 
        // dram_data_id 4 times it's considered done
        // Would need to know how many packets to expect before considering when it's done. Keep track in backend or dram? 

        if(be_sr_wr_req_q.be_sram_wr_req_accepted && (queue_head != queue_tail)) begin
            be_sr_wr_req_q.sram_write_req = sram_wr_req_latch_block[req_queue[queue_head]];
            nxt_sram_latch_set = 0; // invalidate the set
            nxt_queue_head = queue_head + 1; // increase the queue_head to the next dram_data_id
            // don't have to "invalidate" the previous head of the request queue
            // The head can only move if we have a valid in the head anyways
        end

        if((queue_tail + 1) == queue_head) begin 
            nxt_sram_latch_set = ;
            nxt_queue_tail = fifo_tail;
            be_sr_wr_req_q.sram_write_req_latched = 1'b0;
            be_sr_wr_req_q.sram_write_queue_full = 1'b1;
        end

    end

endmodule
