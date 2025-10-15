`ifndef SCPAD_PKG_SV
`define SCPAD_PKG_SV

package scpad_pkg;
    `include "scpad_params.svh"
    `include "xbar_params.svh"

    //////////////////////////////////////////////////////////////////////
    ///////////////////////// Derived Parameters /////////////////////////
    //////////////////////////////////////////////////////////////////////

    localparam int MAX_DIM_WIDTH  = $clog2(NUM_COLS); // bit length
    localparam int XBAR_LATENCY = (XBAR_TYPE == "BENES") ? BENES_LATENCY : 
                                (XBAR_TYPE == "BATCHER") ? BATCHER_LATENCY :  NAIVE_LATENCY;
    localparam int ELEM_BYTES  = ELEM_BITS/8; // always a multiple of 8        
    localparam int ROW_BYTES = (NUM_COLS * ELEM_BITS)/8;   
    localparam int NUM_ROWS = SCPAD_SIZE_BYTES / ROW_BYTES;  // num slots in each bank 

    localparam int SCPAD_ADDR_WIDTH = $clog2(SCPAD_SIZE_BYTES); // imagine scpad is flattened, and then addressable. 

    localparam int ROW_IDX_WIDTH  = $clog2(NUM_ROWS);
    localparam int COL_IDX_WIDTH = $clog2(NUM_COLS);

    localparam int ROW_SHIFT = $clog2(ROW_BYTES);    
    localparam int ELEM_SHIFT = $clog2(ELEM_BYTES);        

    localparam int SCPAD_ID_WIDTH = $clog2(NUM_SCPADS);

    //////////////////////////////////////////////////////////////////////
    /////////////////////////// Helper Functions /////////////////////////
    //////////////////////////////////////////////////////////////////////

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

    //////////////////////////////////////////////////////////////////////
    ////////////////////////////////// Enums /////////////////////////////
    //////////////////////////////////////////////////////////////////////

    typedef logic [NUM_COLS-1:0] mask_t;    
    typedef logic [NUM_COLS-1:0][ELEM_BITS-1:0] scpad_data_t;      
    typedef logic [NUM_COLS-1:0][COL_IDX_WIDTH-1:0] shift_mask_t; 
    typedef logic [NUM_COLS-1:0][ROW_IDX_WIDTH-1:0] slot_mask_t; 

    typedef enum logic { SRC_FE = 1'b0, SRC_BE = 1'b1 } src_t;

    // Scheduler FU <=> Backend
    typedef struct packed {
        logic write;
        logic [SCPAD_ADDR_WIDTH-1:0] spad_addr;
        logic [MAX_DIM_WIDTH-1:0] num_rows;
        logic [MAX_DIM_WIDTH-1:0] num_cols;
        logic [MAX_DIM_WIDTH-1:0] row_id;
        logic [MAX_DIM_WIDTH-1:0] col_id;
        logic row_or_col;
        logic [SCPAD_ID_WIDTH-1:0]   scpad_id;
    } sched_req_t;

    typedef struct packed {
        logic accepted;
    } sched_res_t;

    // DRAM Cntrl. <=> Backend
    typedef struct packed {
        logic write;
        logic [DRAM_ID_WIDTH-1:0]   id;
        logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
        logic [COL_IDX_WIDTH-1:0]   num_bytes;
        scpad_data_t                wdata;
    } dram_req_t;

    typedef struct packed {
        logic complete;
        logic [DRAM_ID_WIDTH-1:0] id;
        scpad_data_t              rdata;
    } dram_res_t;

    // Crossbar descriptors
    typedef struct packed {
        slot_mask_t slot_mask;
        shift_mask_t shift_mask;
        mask_t valid_mask;
    } xbar_desc_t;

    // FE/BE request/response structures
    typedef struct packed {
        logic [SCPAD_ADDR_WIDTH-1:0] addr;
        logic [MAX_DIM_WIDTH-1:0] num_rows;
        logic [MAX_DIM_WIDTH-1:0] num_cols;
        logic [MAX_DIM_WIDTH-1:0] row_id;
        logic [MAX_DIM_WIDTH-1:0] col_id;
        logic row_or_col;
        xbar_desc_t xbar;
    } rd_req_t;

    typedef struct packed {
        logic  complete;
        scpad_data_t rdata;
    } rd_res_t;

    typedef struct packed {
        logic [SCPAD_ADDR_WIDTH-1:0] addr;
        logic [MAX_DIM_WIDTH-1:0] num_rows;
        logic [MAX_DIM_WIDTH-1:0] num_cols;
        logic [MAX_DIM_WIDTH-1:0] row_id;
        logic [MAX_DIM_WIDTH-1:0] col_id;
        logic row_or_col;
        xbar_desc_t xbar;
        scpad_data_t wdata;
    } wr_req_t;

    typedef struct packed {
        logic complete;
    } wr_res_t;

    // Router BE > FE selected requests/responses
    typedef struct packed {
        logic  valid;
        src_t    src;
        xbar_desc_t  xbar;
        scpad_data_t wdata;
    } sel_wr_req_t;

    typedef struct packed {
        logic valid; 
        src_t src;
    } sel_wr_res_t;

    typedef struct packed {
        logic valid;
        src_t src;
        xbar_desc_t xbar;
    } sel_rd_req_t;

    typedef struct packed {
        logic valid; 
        src_t src;
        scpad_data_t rdata;
    } sel_rd_res_t;


endpackage

`endif
