/*
    Unified scratchpad interface (V4)
    
    Interfaces are defined as arrays. 
    Module instances can be parameterised with an `idx` value and slice the appropriate
    element of each array internally.  
    Body contains Head, Tail, XBARs, SRAM controller.
    Head does request arbitration (BE > FE priority) and stalls FE/BE if downstream is stalled.
    Tail does response arbitration/demux (FE/BE round-robin) and does not
    stall.  
    XBARs route requests/responses between Head/Tail and SRAM controller.
    SRAM controller is trivial. 
    FE/BE can be stalled by Body if Body is stalled. Very uncommon case. Backpressure FIFO is large enough to compensate.
    
    Author: Akshath Raghav Ravikiran
*/

`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface scpad_if;
    import spad_types_pkg::*;

    // ----------------------------------------------------------------------
    // Struct Definitions
    // ----------------------------------------------------------------------

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


    // ----------------------------------------------------------------------
    // Wires
    // ----------------------------------------------------------------------

    // Backend <=> DRAM Cntrl.
    logic be_dram_stall [NUM_SCPADS];
    logic be_dram_req_valid [NUM_SCPADS];
    dram_req_t be_dram_req [NUM_SCPADS];
    logic dram_be_res_valid [NUM_SCPADS];
    dram_res_t dram_be_res [NUM_SCPADS];

    // Scheduler <=> Backend 
    logic sched_req_valid [NUM_SCPADS];
    sched_req_t sched_req [NUM_SCPADS];
    logic sched_res_valid [NUM_SCPADS];
    sched_res_t sched_res [NUM_SCPADS];

    // Backend <=> Body channels 
    logic be_stall [NUM_SCPADS]; 
    // Read channels
    logic  be_rd_req_valid [NUM_SCPADS];
    rd_req_t  be_rd_req  [NUM_SCPADS];
    logic  be_rd_res_valid [NUM_SCPADS];
    rd_res_t  be_rd_res  [NUM_SCPADS];
    // Write channels
    logic  be_wr_req_valid [NUM_SCPADS];
    wr_req_t  be_wr_req [NUM_SCPADS];
    logic  be_wr_res_valid [NUM_SCPADS];
    wr_res_t  be_wr_res  [NUM_SCPADS];

    // Vector <=> Frontend channels
    logic fe_vec_stall [NUM_SCPADS];
    // Read channels
    logic  vec_rd_req_valid   [NUM_SCPADS];
    rd_req_t  vec_rd_req  [NUM_SCPADS];
    logic vec_rd_res_valid [NUM_SCPADS];
    rd_res_t vec_rd_res [NUM_SCPADS];
    // Write channels
    logic  vec_wr_req_valid   [NUM_SCPADS];
    wr_req_t  vec_wr_req  [NUM_SCPADS];
    logic   vec_wr_res_valid   [NUM_SCPADS];
    wr_res_t vec_wr_res  [NUM_SCPADS];

    // Frontend <=> Body channels
    logic fe_stall [NUM_SCPADS];
    // Read channels
    logic  fe_rd_req_valid [NUM_SCPADS];
    rd_req_t  fe_rd_req [NUM_SCPADS];
    logic  fe_rd_res_valid [NUM_SCPADS];
    rd_res_t  fe_rd_res  [NUM_SCPADS];
    // Write channels
    logic  fe_wr_req_valid [NUM_SCPADS];
    wr_req_t  fe_wr_req [NUM_SCPADS];
    logic  fe_wr_res_valid [NUM_SCPADS];
    wr_res_t  fe_wr_res  [NUM_SCPADS];

    // Head <=> Stomach <=> Tail 
    logic w_stall [NUM_SCPADS]; 
    logic r_stall [NUM_SCPADS]; 

    // Head => Stomach => Tail (Write)
    sel_wr_req_t head_stomach_wr_req [NUM_SCPADS]; // into wr xbar
    sel_wr_req_t xbar_cntrl_wr_req [NUM_SCPADS]; // into body fifo 
    sel_wr_req_t cntrl_spad_wr_req [NUM_SCPADS]; // into spad 
    sel_wr_res_t stomach_tail_wr_res [NUM_SCPADS]; // into tail 

    // Head => Stomach => Tail (Read)
    sel_rd_req_t head_stomach_rd_req [NUM_SCPADS]; //  into body fifo
    sel_rd_req_t cntrl_spad_rd_req [NUM_SCPADS]; // into spad
    sel_rd_res_t spad_xbar_rd_req [NUM_SCPADS]; // into rd xbar
    sel_rd_res_t stomach_tail_rd_res [NUM_SCPADS]; // into tail 

    // Spad Done.
    mask_t spad_cntrl_rd_res [NUM_SCPADS]; 
    mask_t spad_cntrl_wr_res [NUM_SCPADS]; 

    // ----------------------------------------------------------------------
    // External Modport definitions
    // ----------------------------------------------------------------------

    modport dram_backend (
        input be_dram_req_valid, be_dram_req,
        input be_dram_stall,
        output dram_be_res_valid, dram_be_res
    );

    modport vec_frontend (
        input  fe_vec_stall,
        output vec_rd_req_valid, vec_rd_req,
        output vec_wr_req_valid, vec_wr_req,
        input  vec_rd_res_valid, vec_rd_res,
        input  vec_wr_res_valid, vec_wr_res
    );

    modport sched_backend (
        output sched_req_valid, sched_req,
        input  sched_res_valid, sched_res
    );

    // ----------------------------------------------------------------------
    // Internal Modport definitions
    // ----------------------------------------------------------------------

    // Scheduler <=> Backend
    modport backend_sched (
        input  sched_req_valid, sched_req,
        output sched_res_valid, sched_res
    );

    // Backend <=> Body
    modport backend_body (
        // Body can stall backend
        input  be_stall,
        // READ 
        output be_rd_req_valid, be_rd_req,
        input  be_rd_res_valid, be_rd_res,
        // WRITE 
        output be_wr_req_valid, be_wr_req,
        input  be_wr_res_valid, be_wr_res
    );

    // Backend <=> DRAM
    modport backend_dram (
        output be_dram_req_valid, be_dram_req,
        output  be_dram_stall,
        input dram_be_res_valid, dram_be_res
    );

    // Vec. Core <=> Frontend 
    modport frontend_vec (
        output fe_vec_stall,
        input  vec_rd_req_valid, vec_rd_req,
        input  vec_wr_req_valid, vec_wr_req,
        output vec_rd_res_valid, vec_rd_res,
        output vec_wr_res_valid, vec_wr_res
    );

    // Frontend <=> Body
    modport frontend_body (
        input fe_stall,
        // READ
        output fe_rd_req_valid, fe_rd_req,
        input  fe_rd_res_valid, fe_rd_res,
        // WRITE 
        output fe_wr_req_valid, fe_wr_req,
        input  fe_wr_res_valid, fe_wr_res
    );

    // Write crossbar
    modport xbar_w (
        input w_stall,
        input head_stomach_wr_req,
        output xbar_cntrl_wr_req
    );

    // Read crossbar
    modport xbar_r (
        input r_stall,
        input spad_xbar_rd_req,
        output stomach_tail_rd_res
    );

    // SRAM Controller
    modport sram_ctrl (
        output w_stall, r_stall,
        // READ path
        input  head_stomach_rd_req,
        output cntrl_spad_rd_req,
        input  spad_cntrl_rd_res,
        output spad_xbar_rd_req
        // WRITE path
        input  xbar_cntrl_wr_req,
        output cntrl_spad_wr_req,
        input  spad_cntrl_wr_res,
        output stomach_tail_wr_res,
    );

    // Head (Req MUX with BE > FE priority) per scratchpad
    modport spad_head (
        // Downstream backpressure
        input w_stall, r_stall,
        // Header backpresssure. 
        output fe_stall, be_stall
        // Inputs from FE and BE
        input  fe_rd_req_valid, fe_rd_req,
            fe_wr_req_valid, fe_wr_req,
            be_rd_req_valid, be_rd_req,
            be_wr_req_valid, be_wr_req,
        // Outputs toward Body
        output head_stomach_wr_req, head_stomach_rd_req,

    );

    // Tail (Resp Arb/Demux back to FE/BE) per scratchpad
    // Won't stall. 
    modport spad_tail (
        input  stomach_tail_wr_res, stomach_tail_rd_res,
        output fe_wr_res_valid, fe_wr_res,
            fe_rd_res_valid, fe_rd_res,
            be_wr_res_valid, be_wr_res,
            be_rd_res_valid, be_rd_res
    );

    // Body: Head <=> XBARs <=> SRAM ctrl <=> XBARs <=> Tail 
    modport spad_body (
        // Inputs from FE/BE
        input  fe_rd_req_valid, fe_rd_req,
            fe_wr_req_valid, fe_wr_req,
            be_rd_req_valid, be_rd_req,
            be_wr_req_valid, be_wr_req,
        // Outputs back to FE/BE
        output fe_stall, be_stall,
            fe_wr_res_valid, fe_wr_res,
            fe_rd_res_valid, fe_rd_res,
            be_wr_res_valid, be_wr_res,
            be_rd_res_valid, be_rd_res
    );

    // ----------------------------------------------------------------------
    // Top-level modport 
    // ----------------------------------------------------------------------
    modport top (
        // Scheduler <=> Backend
        output sched_req_valid, sched_req,
        input  sched_res_valid, sched_res,

        // Backend <=> DRAM
        output be_dram_req_valid, be_dram_req,
        input  be_dram_stall,
        input  dram_be_res_valid, dram_be_res,

        // Vector Core <=> Frontend
        input  vec_rd_req_valid, vec_rd_req,
        input  vec_wr_req_valid, vec_wr_req,
        output vec_rd_res_valid, vec_rd_res,
        output vec_wr_res_valid, vec_wr_res,
        input  fe_vec_stall
    );


endinterface

`endif 
