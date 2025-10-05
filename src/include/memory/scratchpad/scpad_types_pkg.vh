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

package spad_types_pkg;
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

    localparam int DRAM_ID_WIDTH = 6; 
    typedef enum logic { SRC_FE = 1'b0, SRC_BE = 1'b1 } src_t;

    typedef logic [NUM_COLS-1:0][ELEM_BITS-1:0] scpad_data_t;      
    typedef logic [NUM_COLS-1:0] enable_mask_t;    
    typedef logic [NUM_COLS-1:0][COL_IDX_WIDTH-1:0] shift_mask_t; 
    typedef logic [NUM_COLS-1:0][ROW_IDX_WIDTH-1:0] slot_mask_t; 


endpackage
`endif
