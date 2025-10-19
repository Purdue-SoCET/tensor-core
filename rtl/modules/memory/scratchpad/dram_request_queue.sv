`include "scpad_pkg.sv"
`include "scpad_if.sv"
`include "dram_req_queue_if.vh"

    // modport baceknd_dram_req_queue ( 
    //     input dram_addr, id, num_bytes, sram_rdata, sram_res_valid
    //     input sched_write,       // scheduler write = 1 means it's a scpad store aka we need to do a dram write.
    //     input be_stall,
    //     input dram_be_stall,     // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
    //                               // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
    //     output dram_req, dram_queue_full, dram_req_latched
    // );

module dram_request_queue ( // UUID now needs to have 2 lower bits for an offest since dram can only handle 64 bits at a time
    input logic clk, n_rst, 
    dram_req_queue_if.baceknd_dram_req_queue be_dr_req_q
);
    import scpad_pkg::*;

    // typedef struct packed {
    //     logic valid; 
    //     logic write;
    //     logic [DRAM_ID_WIDTH-1:0]   id;
    //     logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //     logic [COL_IDX_WIDTH-1:0]   num_bytes;
    //     scpad_data_t wdata;
    // } dram_req_t;

    dram_req_t [DRAM_ID_WIDTH-1:0] dram_req_latch_block; 
    dram_req_t nxt_dram_head_latch_set, nxt_dram_tail_latch_set;

    logic [DRAM_ID_WIDTH-1:0] fifo_head, nxt_fifo_head, fifo_tail, nxt_fifo_tail;
    logic [2:0] request_completed_counter, nxt_request_completed_counter;
    
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            dram_req_latch_block <= 'b0;
            fifo_head <= 'b0;
            fifo_tail <= 'b0;
            request_completed_counter <= 'b0;
        end else begin
            dram_req_latch_block[fifo_head] <= nxt_dram_head_latch_set;
            dram_req_latch_block[fifo_tail] <= nxt_dram_tail_latch_set;
            fifo_head <= nxt_fifo_head;
            fifo_tail <= nxt_fifo_tail
            request_completed_counter <= nxt_request_completed_counter;
        end
    end

    always_comb begin
        be_dr_req_q.dram_req = 0;
        be_dr_req_q.transaction_complete = 1'b0;

        nxt_dram_head_latch_set = dram_req_latch_block[fifo_head];
        nxt_dram_tail_latch_set = dram_req_latch_block[fifo_tail];
        nxt_fifo_head = fifo_head;
        nxt_fifo_tail = fifo_tail;
        nxt_request_completed_counter = request_completed_counter;

        be_dr_req_q.dram_queue_full = 1'b0;
        be_dr_req_q.burst_complete = 1'b0;

        if(be_dr_req_q.sched_write == 1'b1) begin // sched write is 1 when doing a scpad store, aka sram read to dram write
            if(be_dr_req_q.sram_res_valid == 1'b1) begin
                nxt_dram_tail_latch_set.valid = 1'b1;
                nxt_dram_tail_latch_set.write = be_dr_req_q.sched_write;
                nxt_dram_tail_latch_set.id = {be_dr_req_q.id, be_dr_req_q.sub_id};
                nxt_dram_tail_latch_set.dram_addr = be_dr_req_q.dram_addr;
                nxt_dram_tail_latch_set.num_bytes = be_dr_req_q.num_bytes;
                nxt_dram_tail_latch_set.wdata = be_dr_req_q.sram_rdata;
                nxt_fifo_tail = fifo_tail + 1;
                be_dr_req_q.transaction_complete = 1'b1;
            end
        end else begin // dram read to sram write
            nxt_dram_tail_latch_set.valid = 1'b1;
            nxt_dram_tail_latch_set.write = be_dr_req_q.sched_write;
            nxt_dram_tail_latch_set.id = {be_dr_req_q.id, be_dr_req_q.sub_id};
            nxt_dram_tail_latch_set.dram_addr = be_dr_req_q.dram_addr;
            nxt_dram_tail_latch_set.num_bytes = be_dr_req_q.num_bytes;
            nxt_dram_tail_latch_set.wdata = 0;
            nxt_fifo_tail = fifo_tail + 1;
            nxt_request_completed_counter = request_completed_counter + 1;
            be_dr_req_q.burst_complete = 1'b1;
        end

        if((be_dr_req_q.dram_be_stall == 1'b0) && (fifo_head != fifo_tail)) begin //the dram is accepting request and we aren't empty
            be_dr_req_q.dram_req = dram_req_latch_block[fifo_head];
            nxt_dram_head_latch_set = 0; // invalidate head when our request are accepted.
            nxt_fifo_head = fifo_head + 1;
        end

        if((fifo_tail + 1) == fifo_head) begin 
            nxt_dram_tail_latch_set = dram_req_latch_block[fifo_tail];
            nxt_fifo_tail = fifo_tail;
            be_dr_req_q.dram_req_latched = 1'b0;
            be_dr_req_q.dram_queue_full = 1'b1;
        end

        if(nxt_request_completed_counter == be_dr_req_q.num_request) begin
            be_dr_req_q.transaction_complete = 1'b1;
            nxt_request_completed_counter = 0;
        end
    
    end

endmodule
