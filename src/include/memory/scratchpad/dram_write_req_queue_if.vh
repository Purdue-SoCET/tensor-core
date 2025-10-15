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
    logic [DRAM_ID_WIDTH-1:0] sram_data_id;
    scpad_data_t sr_rdata;
    logic be_dram_rd_req_complete
    logic dram_write_queue_full, dram_write_req_latched, be_dram_wr_req_accepted;

    modport baceknd_dram_write_req_queue ( 
        input dram_addr, sram_data_id, num_bytes, sr_rdata, be_dram_wr_req_accepted,
        input be_dram_rd_req_complete,

        output dram_write_req, dram_write_queue_full, dram_write_req_latched
    );

endinterface

`endif //SRAM_WRITE_REQ_QUEUE_IF