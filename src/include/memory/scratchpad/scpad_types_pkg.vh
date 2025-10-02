`ifndef SCPAD_TYPES_PKG_VH
`define SCPAD_TYPES_PKG_VH

// The Scratchpad is a SW Controlled Cache for the AMP1 Tensor Core. It is similar to the Unified Local Buffer in TPUV3 Arch, and is meant to be programmable using TMA-like instrinsics of the Nvidia Hopper arch (supports async copies). 
// The Scratchpad will deal with loading tiles of data (at the maximum of 32x32) from DRAM, and passing them around to Systolic Array and Vector Core units. Specifically, to the TCA and VReg Controller.
// The Micro-Arch RTL of Scratchpad will contain the following units: 
//      1. Backend Prefetcher 
//      2. Frontend Systolic Array 
//      3. Frontend Vector Core 
//      4. Crossbar
//      5. SRAM Controller 
//      6. Frontend Arb. 

package scpad_types_pkg;
    parameter int SCPAD_SIZE_BYTES = 1024*1024;  // total scratchpad size 
    parameter int NUM_COLS = 32;  // always a power of 2 
    parameter int ELEM_BITS = 16;  // fp16 

    parameter int MAX_TILE_SIZE = 32; // M x M 
    localparam int MAX_DIM_WIDTH  = $clog2(MAX_TILE_SIZE); // bit length

    localparam int ELEM_BYTES  = ELEM_BITS/8; // always a multiple of 8        
    localparam int ROW_BYTES = (NUM_COLS * ELEM_BITS)/8;   
    localparam int NUM_ROWS = SCPAD_SIZE_BYTES / ROW_BYTES;  // num slots in each bank 

    localparam int SCPAD_ADDR_WIDTH = $clog2(SCPAD_SIZE_BYTES); // imagine scpad is flattened, and then addressable. 
    parameter int DRAM_ADDR_WIDTH  = 32; 

    localparam int ROW_IDX_WIDTH  = $clog2(NUM_ROWS);
    localparam int COL_IDX_WIDTH = $clog2(NUM_COLS);

    localparam int ROW_SHIFT = $clog2(ROW_BYTES);    
    localparam int ELEM_SHIFT = $clog2(ELEM_BYTES);        

    function automatic void addr_to_row_col(
        input  logic [SCPAD_ADDR_WIDTH-1:0]      byte_addr,
        output logic [ROW_IDX_WIDTH-1:0]   row_idx,
        output logic [COL_IDX_WIDTH-1:0]   col_idx
    );
        row_idx = byte_addr[SCPAD_ADDR_WIDTH-1:ROW_SHIFT];
        col_idx = byte_addr[ROW_SHIFT-1:ELEM_SHIFT];
    endfunction

    function automatic logic [SCPAD_ADDR_WIDTH-1:0] row_col_to_addr(
        input logic [ROW_IDX_WIDTH-1:0] row_idx,
        input logic [COL_IDX_WIDTH-1:0] col_idx
    );
        return (row_idx << ROW_SHIFT) | (col_idx << ELEM_SHIFT);
    endfunction

    // Not editable. Keep at 2. Hardcoded Logic. 
    localparam NUM_SCPADS = 2; 
    localparam int SCPAD_ID_WIDTH = $clog2(NUM_SCPADS);

    typedef logic [NUM_COLS-1:0][ELEM_BITS-1:0] scpad_data_t;      
    typedef logic [NUM_COLS-1:0] enable_mask_t;    
    typedef logic [NUM_COLS-1:0][COL_IDX_WIDTH-1:0] shift_mask_t; 
    typedef logic [NUM_COLS-1:0][ROW_IDX_WIDTH-1:0] slot_mask_t; 

        ////////////////////////////////////////////////////////////////////////////
    // Interaction ID
    typedef enum logic [1:0] {
        FRONTEND_VC1_REQ = 2'b00,
        FRONTEND_VC2_REQ = 2'b01,
        BACKEND_REQ      = 2'b10
    } sram_interaction_id_t;

    ////////////////////////////////////////////////////////////////////////////
    // Crossbar descriptor
    // These element types (slot_mask_t, shift_mask_t, enable_mask_t, scpad_data_t)
    // must be defined in scpad_types_pkg. If different names used there, adapt.
    typedef struct packed {
        slot_mask_t   slot_mask;
        shift_mask_t  shift_mask;
        enable_mask_t valid_mask;
    } xbar_desc_t;

    // SRAM read/write request/response structs
    typedef struct packed {
        sram_interaction_id_t int_id;
        logic valid;
        xbar_desc_t xbar_desc;
        logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    } sram_r_req_t;

    typedef struct packed {
        sram_interaction_id_t int_id;
        logic valid;
        scpad_data_t rdata;
    } sram_r_res_t;

    typedef struct packed {
        sram_interaction_id_t int_id;
        logic valid;
        xbar_desc_t xbar_desc;
        scpad_data_t wdata;
        logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    } sram_w_req_t;

    typedef struct packed {
        sram_interaction_id_t int_id;
        logic valid;
    } sram_w_res_t;

    typedef struct packed {
        logic  valid;
        sram_interaction_id_t int_id;
        logic [NUM_COLS-1:0] mask;
    } inflight_tag_t;

    typedef sram_r_res_t sram_xbar_r_t;

    typedef struct packed {
        logic valid;
        slot_mask_t  slot_mask;
        enable_mask_t valid_mask;
        scpad_data_t wdata;
    } xbar_sram_w_t;

    ////////////////////////////////////////////////////////////////////////////
    // Frontend request / response types (per-VC)
    typedef struct packed {
        logic valid;
        logic write;
        logic [SCPAD_ADDR_WIDTH-1:0] addr;
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols;
        logic [MAX_DIM_WIDTH-1:0] row_id, col_id;
        logic row_or_col;
        logic [SCPAD_ID_WIDTH-1:0] scpad_id;
        scpad_data_t wdata;
    } frontend_req_t;

    typedef struct packed {
        logic valid;
        logic complete;
        scpad_data_t rdata;
    } frontend_res_t;

    ////////////////////////////////////////////////////////////////////////////
    // Backend / DRAM request/res
    typedef struct packed {
        logic valid;
        logic write;
        logic [SCPAD_ADDR_WIDTH-1:0] addr;
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols;
        logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    } scheduler_req_t;

    typedef struct packed {
        logic valid;
        logic complete;
    } scheduler_res_t;

    scheduler_req_t scheduler_backend_req;
    scheduler_res_t backend_scheduler_res;

    typedef struct packed {
        logic valid;
        logic write;
        logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
        logic [COL_IDX_WIDTH-1:0] num_bytes;
        scpad_data_t wdata;
    } dram_req_t;

    typedef struct packed {
        logic valid;
        logic complete;
        scpad_data_t rdata;
    } dram_res_t;

endpackage
`endif
