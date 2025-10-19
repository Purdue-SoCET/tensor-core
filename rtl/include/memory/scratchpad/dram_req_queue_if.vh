`ifndef DRAM_REQ_QUEUE_IF
`define DRAM_REQ_QUEUE_IF

`include "scpad_pkg.sv"
`include "scpad_if.sv"

interface dram_req_queue_if;
    import scpad_pkg::*;

    typedef struct packed {
        logic valid; 
        logic write;
        logic [7:0]   id;
        logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
        logic [COL_IDX_WIDTH-1:0]   num_bytes;
        scpad_data_t wdata;
    } dram_req_t;

    logic sched_write;
    dram_req_t dram_req;
    logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    logic [DRAM_ID_WIDTH-1:0]   id;
    logic [2:0]   sub_id, num_request;
    logic [COL_IDX_WIDTH-1:0]   num_bytes;
    scpad_data_t sram_rdata;
    logic be_stall;
    logic be_dram_rd_req_complete;
    logic dram_queue_full, transaction_complete, dram_be_stall, sram_res_valid, burst_complete;

    modport baceknd_dram_req_queue ( 
        input dram_addr, id, sub_id, num_bytes, sram_rdata, sram_res_valid, num_request,
        input sched_write,       // scheduler write = 1 means it's a scpad store aka we need to do a dram write.
        input be_stall,
        input dram_be_stall,     // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
                                  // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
        output dram_req, dram_queue_full, transaction_complete, burst_complete
    );

endinterface

`endif //DRAM_REQ_QUEUE_IF