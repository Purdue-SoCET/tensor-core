`ifndef SCPAD_TYPES_PKG_VH
`define SCPAD_TYPES_PKG_VH

package spad_types_pkg;
    parameter int SCPAD_SIZE_BYTES = 1024*1024;  // total scratchpad size 
    parameter int NUM_COLS = 32;  // always a power of 2 
    parameter int ELEM_BITS = 16;  // fp16 
    parameter int MAX_SRAM_DELAY = 3; 

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
    localparam int NUM_SCPADS = 2; 
    localparam int SCPAD_ID_WIDTH = $clog2(NUM_SCPADS);

    localparam int DRAM_ID_WIDTH = 6; 
    typedef enum logic { SRC_FE = 1'b0, SRC_BE = 1'b1 } src_t;

    typedef logic [NUM_COLS-1:0] mask_t;    
    typedef logic [NUM_COLS-1:0][ELEM_BITS-1:0] scpad_data_t;      
    typedef logic [NUM_COLS-1:0][COL_IDX_WIDTH-1:0] shift_mask_t; 
    typedef logic [NUM_COLS-1:0][ROW_IDX_WIDTH-1:0] slot_mask_t; 

    typedef enum { "NAIVE", "BENES", "BATCHER" } xbar_types_t;
    parameter xbar_types_t MODE = "NAIVE";
    parameter int XBAR_LATENCY = 14; 

endpackage
`endif
