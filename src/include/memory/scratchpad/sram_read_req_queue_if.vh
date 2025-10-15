`ifndef SRAM_READ_REQ_QUEUE_IF
`define SRAM_READ_REQ_QUEUE_IF

`include "scpad_types_pkg.vh"

interface sram_read_req_queue_if;
    import scpad_types_pkg::*;

    typedef struct packed {
        slot_mask_t    slot_mask; // per-col row/slot indices feeding banks
        shift_mask_t   shift_mask; // per-col shift/bank mapping
        enable_mask_t  valid_mask;  // per-col enable/valid
    } xbar_desc_t;

    typedef struct packed {
            logic        valid;     
            logic        row_or_col;        
            xbar_desc_t  xbar;
    } sram_read_req_t;

    sram_read_req_t sram_read_req;
    logic [DRAM_ID_WIDTH-1:0] id;
    xbar_desc_t  xbar_desc;
    logic be_dr_r_req_accepted, sched_write;
    logic sram_read_queue_full, sram_read_req_latched, be_sram_rd_req_accepted;

    modport baceknd_sram_read_req_queue ( 
        input xbar_desc, id, be_dr_r_req_accepted,
        input sched_write
        input be_sram_rd_req_accepted,

        output sram_read_req, sram_read_queue_full, sram_read_req_latched
    );

endinterface

`endif //SRAM_READ_REQ_QUEUE_IF