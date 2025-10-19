`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "dram_read_req_queue_if.vh"

    // modport baceknd_dram_read_req_queue ( 
    //     input  dram_addr, id, num_bytes,
    //     input  sched_write,       // scheduler write = 0 means it's a scpad load aka we need to do a dram read.
    //     input  be_dram_req_accepted, // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
    //                               // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
    //     output be_dram_read_req, dram_read_queue_full, dram_read_req_latched
    // );

module dram_read_request_queue ( // UUID now needs to have 2 lower bits for an offest since dram can only handle 64 bits at a time
    input logic clk, n_rst, 
    dram_read_req_queue.baceknd_dram_read_req_queue be_dr_rd_req_q
);
    import scpad_types_pkg::*;

    // typedef struct packed {
    //         logic       valid;     
    //         logic [DRAM_ID_WIDTH-1:0]   id;         
    //         logic [DRAM_ADDR_WIDTH-1:0] dram_addr; 
    //         logic [COL_IDX_WIDTH-1:0]   num_bytes;  
    // } dram_read_req_t;

    dram_read_req_t [DRAM_ID_WIDTH-1:0] dram_rd_req_latch_block; // 32 frames
    dram_read_req_t nxt_dram_head_latch_set, nxt_dram_tail_latch_set;

    logic [DRAM_ID_WIDTH-1:0] fifo_head, nxt_fifo_head, fifo_tail, nxt_fifo_tail;
    
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            dram_rd_req_latch_block <= 'b0;
            fifo_head <= 'b0;
            fifo_tail <= 'b0;
        end else begin
            dram_rd_req_latch_block[fifo_head] <= nxt_dram_head_latch_set;
            dram_rd_req_latch_block[fifo_tail] <= nxt_dram_tail_latch_set;
            fifo_head <= nxt_fifo_head;
            fifo_tail <= nxt_fifo_tail
        end
    end

    always_comb begin
        nxt_dram_head_latch_set = dram_rd_req_latch_block[fifo_head];
        nxt_dram_tail_latch_set = dram_rd_req_latch_block[fifo_tail];
        be_dr_rd_req_q.be_dram_read_req = 0;
        nxt_fifo_head = fifo_head;
        nxt_fifo_tail = fifo_tail;
        dram_read_req_latched = 1'b0;
        be_dr_rd_req_q.dram_read_queue_full = 1'b0;

        if(be_dr_rd_req_q.sched_write == 1'b0) begin
            nxt_dram_tail_latch_set.valid = 1'b1;
            nxt_dram_tail_latch_set.id = be_dr_rd_req_q.id;
            nxt_dram_tail_latch_set.dram_addr = be_dr_rd_req_q.dram_addr;
            nxt_dram_tail_latch_set.num_bytes = be_dr_rd_req_q.num_bytes;
            nxt_fifo_tail = fifo_tail + 1;
            be_dr_rd_req_q.dram_read_req_latched = 1'b1;
        end

        if(be_dr_rd_req_q.be_dram_req_accepted && (fifo_head != fifo_tail)) begin //the dram is accepting request and we aren't empty
            be_dr_rd_req_q.be_dram_read_req = dram_rd_req_latch_block[fifo_head];
            nxt_dram_head_latch_set = 0; // invalidate head when our request are accepted.
            nxt_fifo_head = fifo_head + 1;
        end

        if((fifo_tail + 1) == fifo_head) begin 
            nxt_dram_tail_latch_set = dram_rd_req_latch_block[fifo_tail];
            nxt_fifo_tail = fifo_tail;
            be_dr_rd_req_q.dram_read_req_latched = 1'b0;
            be_dr_rd_req_q.dram_read_queue_full = 1'b1;
        end

    

    end
    

endmodule
