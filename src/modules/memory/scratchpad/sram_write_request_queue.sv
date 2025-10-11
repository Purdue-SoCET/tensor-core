`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "sram_write_req_queue.vh"

    // modport baceknd_dram_read_req_queue ( 
    //     input  dram_addr, id, num_bytes,
    //     input  sched_write,       // scheduler write = 1 means it's a scpad load aka we need to do a dram read.
    //     input  be_dram_req_ready, // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
    //                               // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
    //     output be_dram_read_req
    // );

module sram_write_request_queue (
    input logic clk, n_rst, dram_read_req_queue.baceknd_dram_read_req_queue be_dr_req_q
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

    logic [DRAM_ID_WIDTH-1:0][DRAM_ID_WIDTH-1:0] req_queue, nxt_req_queue;
    logic [DRAM_ID_WIDTH-1:0] queue_tail, nxt_queue_tail; 
    // The request queue will keep track of what the current latch to send out should be
    // There are 32 latches so need to track of an array of size 32 with the elements being ints that go up to 32.
    // elements are shifted out as they are consumed and the tail keeps track of where to add elements and whether we are full.
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            sram_wr_req_latch_block <= '0;
            req_queue  <= '0;
            queue_tail <= '0;
        end else begin
            sram_wr_req_latch_block[be_dr_req_q.id] <= nxt_sram_latch_set;
            req_queue  <= nxt_req_queue;  // shift out 0th element when consumed otherwise same
            queue_tail <= nxt_queue_tail; // increment tail whenever a req is added
                                          // decrement tail whenever a req is consumed
        end
    end
    always_comb begin

    end

endmodule
