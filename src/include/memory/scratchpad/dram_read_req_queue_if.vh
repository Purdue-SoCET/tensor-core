`ifndef DRAM_READ_REQ_QUEUE_IF
`define DRAM_READ_REQ_QUEUE_IF

`include "scpad_types_pkg.vh"

//  modport backend_dram_ports (
//         output be_dram_req_valid, be_dram_req,
//         input  be_dram_req_ready,
//         input  dram_be_res_valid, dram_be_res,
//         output dram_be_res_ready
//         );


interface dram_read_req_queue_if;
    import scpad_types_pkg::*;

    typedef struct packed {
            logic       valid;     
            logic [DRAM_ID_WIDTH-1:0]   id;         
            logic [DRAM_ADDR_WIDTH-1:0] dram_addr; 
            logic [COL_IDX_WIDTH-1:0]   num_bytes;  
    } dram_read_req_t;

    logic sched_write;
    logic be_dram_req_ready, dram_be_res_valid; 
    logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    logic [DRAM_ID_WIDTH-1:0]   id;
    logic [COL_IDX_WIDTH-1:0]   num_bytes;

    dram_read_req_t be_dram_read_req;

    modport baceknd_dram_read_req_queue ( 
        input  dram_addr, id, num_bytes,
        input  sched_write,       // scheduler write = 1 means it's a scpad load aka we need to do a dram read.
        input  be_dram_req_ready, // tells us if the dram is ready to accept our req. If it is and our FIFO is valid then we can assume 
                                  // our current req will be successfully latched in the dram controller and can invalidate nxt cycle
        output be_dram_read_req
    );

endinterface

`endif //DRAM_READ_REQ_QUEUE_IF