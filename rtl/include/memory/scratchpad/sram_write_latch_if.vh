`ifndef SRAM_WRITE_LATCH_IF
`define SRAM_WRITE_LATCH_IF

`include "scpad_pkg.sv"
`include "scpad_if.sv"

interface sram_write_latch_if;
    import scpad_pkg::*;

    logic [7:0] dram_id;
    xbar_desc_t xbar;
    logic [2:0] num_request; // max number of request is 8 because (32*16)/64 = 8
    sram_write_req_t sram_write_req;
    logic dram_res_valid;
    logic be_stall;
    logic [63:0] dram_rddata; // DRAM BUS can only send 64 bits at a time.
    logic sram_write_req_latched;
    logic [SCPAD_ADDR_WIDTH-1:0] spad_addr;

    modport sram_write_latch (
        input dram_id, dram_res_valid, xbar, dram_rddata, num_request,
        input be_stall, spad_addr,
        output sram_write_req, sram_write_req_latched
    );

endinterface

`endif //SRAM_WRITE_LATCH_IF