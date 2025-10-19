`ifndef SRAM_WRITE_REQ_QUEUE_IF
`define SRAM_WRITE_REQ_QUEUE_IF

`include "scpad_types_pkg.vh"

interface sram_write_req_queue_if;
    import scpad_types_pkg::*;

    typedef struct packed {
            logic       valid;         
            logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
            logic [COL_IDX_WIDTH-1:0]   num_bytes; 
            scpad_data_t wdata;
    } dram_write_req_t;

    dram_write_req_t dram_write_req;
    logic [DRAM_ID_WIDTH-1:0] id;
    scpad_data_t sr_rdata;
    logic be_dram_rd_req_complete
    logic dram_write_queue_full, dram_write_req_latched, be_dram_wr_req_accepted;

    modport baceknd_dram_write_req_queue ( 
        input  dram_addr, id, num_bytes, sram_rdata
        input  sched_write,       // scheduler write = 1 means it's a scpad store aka we need to do a dram write.
        input  be_dram_stall, // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
                                  // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
        output be_dram_read_req, dram_read_queue_full, dram_write_req_latched
    );

endinterface

`endif //SRAM_WRITE_REQ_QUEUE_IF