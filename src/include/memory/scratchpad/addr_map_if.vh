`ifndef ADDR_MAP_IF
`define ADDR_MAP_IF

`include "scpad_types_pkg.vh"

interface addr_map_if;
    import scpad_types_pkg::*; 


    typedef struct packed {
        slot_mask_t    slot_mask; // per-col row/slot indices feeding banks
        shift_mask_t   shift_mask; // per-col shift/bank mapping
        enable_mask_t  valid_mask;  // per-col enable/valid
    } xbar_desc_t;

    logic row_or_col;
    logic [SCPAD_ADDR_WIDTH-1:0] spad_addr;
    logic [MAX_DIM_WIDTH-1:0]    num_rows, num_cols, row_id, col_id;

    xbar_desc_t xbar_desc;

    modport backend_addr (
        input  row_or_col,
        input  spad_addr,
        input  num_rows, num_cols, row_id, col_id,

        output xbar_desc
    );

endinterface

`endif //ADDR_MAP_IF