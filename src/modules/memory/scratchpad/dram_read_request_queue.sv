`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "dram_read_req_queue.vh"

    // modport baceknd_dram_read_req_queue ( 
    //     input  dram_addr, id, num_bytes,
    //     input  sched_write,       // scheduler write = 1 means it's a scpad load aka we need to do a dram read.
    //     input  be_dram_req_ready, // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
    //                               // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
    //     output be_dram_read_req
    // );

module dram_read_request_queue (
    input logic clk, n_rst, dram_read_req_queue.baceknd_dram_read_req_queue be_dr_req_q
);
    import scpad_types_pkg::*;

    // typedef struct packed {
    //         logic       valid;     
    //         logic [DRAM_ID_WIDTH-1:0]   id;         
    //         logic [DRAM_ADDR_WIDTH-1:0] dram_addr; 
    //         logic [COL_IDX_WIDTH-1:0]   num_bytes;  
    // } dram_read_req_t;

    dram_read_req_t [DRAM_ID_WIDTH-1:0] dram_rd_req_latch_block;
    dram_read_req_t nxt_dram_latch_set;

    logic [DRAM_ID_WIDTH-1:0] fifo_head, nxt_fifo_head; 
    // The fifo head keeps track of what the current req
    // we need to send out is
    // be_dr_req_q.id is the index of the set we need to
    // manipulate
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            dram_queue <= '0;
            fifo_head <= '0;
        end else begin
            dram_queue[be_dr_req_q.id] <= nxt_dram_q_set
            fifo_head <= nxt_fifo_head
        end
    end

    always_comb begin

    end
    

endmodule
