`ifndef DRAM_WRITE_LATCH_IF
`define DRAM_WRITE_LATCH_IF

`include "scpad_pkg.sv"
`include "scpad_if.sv"

interface dram_write_latch_if;
    import scpad_pkg::*;

    // typedef struct packed {
    //     logic valid; 
    //     logic [63:0] wdata;
    //     logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //     logic [COL_IDX_WIDTH-1:0]   num_bytes;
    // } dram_write_req_t;

    logic [7:0] dram_id;
    scpad_data_t sram_rddata;
    logic [2:0] num_request; // max number of request is 8 because (32*16)/64 = 8
    dram_write_req_t dram_write_req;
    logic dram_write_latch_busy;
    logic dram_valid, dram_write;
    logic be_stall;
    logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    logic [COL_IDX_WIDTH-1:0]   num_bytes;
    logic dram_write_req_latched;
    logic dram_be_stall;

    modport dram_write_latch (
        input dram_addr, num_bytes, dram_valid, dram_write, sram_rddata, num_request,
        input be_stall, dram_be_stall,
        output dram_write_req, dram_write_latch_busy, dram_write_req_latched
    );

endinterface

`endif //DRAM_WRITE_LATCH_IF