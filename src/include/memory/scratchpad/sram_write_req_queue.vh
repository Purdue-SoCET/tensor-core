`ifndef SRAM_WRITE_REQ_QUEUE_IF
`define SRAM_WRITE_REQ_QUEUE_IF

`include "scpad_types_pkg.vh"

interface sram_write_req_queue_if;
    import scpad_types_pkg::*;

    typedef struct packed {
        slot_mask_t    slot_mask; // per-col row/slot indices feeding banks
        shift_mask_t   shift_mask; // per-col shift/bank mapping
        enable_mask_t  valid_mask;  // per-col enable/valid
    } xbar_desc_t;

    typedef struct packed {
            logic       valid;     
            logic       row_or_col;        
            xbar_desc_t  xbar;  
            scpad_data_t wdata;
    } sram_write_req_t;

    logic [DRAM_ID_WIDTH-1:0]   id;
    xbar_desc_t  xbar;
    scpad_data_t dr_rdata;
    logic be_wr_req_complete

    modport baceknd_sram_write_req_queue ( 
        input  xbar, id, dr_rdata,
        input be_wr_req_complete.

        output sram_write_req_t
    );

endinterface

`endif //SRAM_WRITE_REQ_QUEUE_IF