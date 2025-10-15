`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "dram_write_req_queue_if.vh"

    // modport baceknd_dram_write_req_queue ( 
    //     input dram_addr, sram_data_id, num_bytes, sr_rdata, be_dram_wr_req_accepted,
    //     input be_dram_rd_req_complete,

    //     output dram_write_req, dram_write_queue_full, dram_write_req_latched
    // );

module dram_write_request_queue (
    input logic clk, n_rst, 
    dram_write_req_queue.baceknd_dram_write_req_queue be_dr_wr_req_q
);
    import scpad_types_pkg::*;

    // typedef struct packed {
    //         logic       valid;           
    //         logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //         logic [COL_IDX_WIDTH-1:0]   num_bytes; 
    //         scpad_data_t wdata;
    // } dram_write_req_t;

    dram_write_req [DRAM_ID_WIDTH-1:0] dram_wr_req_latch_block; // 32 latch sets for our queue
    dram_write_req nxt_dram_latch_set;

    logic [DRAM_ID_WIDTH-1:0][DRAM_ID_WIDTH-1:0] req_queue;
    logic [DRAM_ID_WIDTH-1:0] nxt_req_queue, queue_head, nxt_queue_head, queue_tail, nxt_queue_tail; 
    // The request queue will keep track of what the current latch to send out should be
    // There are 32 latches so need to track of an array of size 32 with the elements being ints that go up to 32.
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            dram_wr_req_latch_block <= 'b0;
            req_queue  <= 'b0;
            queue_head <= 'b0;
            queue_tail <= 'b0;
        end else begin
            dram_wr_req_latch_block[be_dr_wr_req_q.sram_data_id] <= nxt_dram_latch_set;
            req_queue[queue_head]  <= nxt_req_queue; 
            queue_head <= nxt_queue_head;
            queue_tail <= nxt_queue_tail;                            
        end
    end

    always_comb begin
        nxt_dram_latch_set = dram_wr_req_latch_block[be_dr_wr_req_q.id];
        nxt_req_queue = req_queue;
        nxt_queue_head = queue_head;
        nxt_queue_tail = queue_tail;
        dram_write_req_latched = 1'b0;
        be_dr_wr_req_q.dram_write_queue_full = 1'b0; 

        if(be_dr_wr_req_q.be_dr_rd_req_complete) begin
            nxt_dram_latch_set.valid = 1'b1;
            nxt_dram_latch_set.num_bytes = be_dr_wr_req_q.num_bytes;
            nxt_dram_latch_set.dram_addr = be_dr_wr_req_q.dram_addr;
            nxt_dram_latch_set.wdata = be_dr_wr_req_q.sr_rdata;
            nxt_req_queue = be_dr_wr_req_q.sram_data_id; 
            nxt_queue_tail = queue_tail + 1;
            be_dr_wr_req_q.dram_write_req_latched = 1'b1;
        end

        if(be_dr_wr_req_q.be_sram_req_accepted) begin
            nxt_dram_latch_set = 0; // invalidate the set
            nxt_queue_head = queue_head + 1; // increase the queue_head to the next id
        end

        if((queue_tail + 1) == queue_head) begin 
            nxt_dram_latch_set = dram_wr_req_latch_block[be_dr_wr_req_q.xbar_data_id];
            nxt_queue_tail = fifo_tail;
            be_dr_wr_req_q.dram_write_req_latched = 1'b0;
            be_dr_wr_req_q.dram_write_queue_full = 1'b1;
        end
        /* 
        Since this queue is based off input from dram read what happens if we recieve a dram 
        read result when its full? Well it shouldn't be likely here but it will be a problem for
        the sram read to dram latch. The dram latch will potentially have to be huge. If the queue
        is full and a result comes in, the way its set up right now then the data will just disappear.
        How to make it not disappear? On an sram write queue stop sending request. Now how many request
        are in flight in the sram/dram already? Maybe tell sram/dram we are full too so it can stop the request
        until the latch can start recieving them. Again shouldn't be a problem for dram -> sram type but will be a problem
        for sram -> dram types.
        */

        be_dr_wr_req_q.dram_write_req = dram_wr_req_latch_block[req_queue[queue_head]];
    end

endmodule
