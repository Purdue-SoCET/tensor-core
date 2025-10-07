/*
    Unified scratchpad interface (V4)
    
    Interfaces are defined as arrays. 
    Module instances can be parameterised with an `idx` value and slice the appropriate
    element of each array internally.  

    Author: Akshath Raghav Ravikiran
*/

`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface scpad_if;
    import spad_types_pkg::*;

    // ----------------------------------------------------------------------
    // Struct Definitions
    // ----------------------------------------------------------------------
    // Crossbar descriptors
    typedef struct packed {
        slot_mask_t   slot_mask;
        shift_mask_t  shift_mask;
        enable_mask_t valid_mask;
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
        scpad_data_twdata;
    } wr_req_t;

    typedef struct packed {
        logic complete;
    } wr_res_t;

    // Router BE>FE selected requests/responses
    typedef struct packed {
        src_t        src;
        xbar_desc_t  xbar;
        scpad_data_t wdata;
    } sel_wr_req_t;

    typedef struct packed {
        src_t src;
    } sel_wr_res_t;

    typedef struct packed {
        src_t      src;
        xbar_desc_t xbar;
    } sel_rd_req_t;

    typedef struct packed {
        src_t        src;
        scpad_data_t rdata;
    } sel_rd_res_t;

    // Crossbar side structs
    typedef struct packed {
        logic   valid;
        enable_mask_t valid_mask;
        slot_mask_t   slot_mask;
        scpad_data_t  wdata;
    } xbar_sram_w_t;

    typedef struct packed {
        logic   valid;
        enable_mask_t valid_mask;
        shift_mask_t  shift_mask;
        scpad_data_t  rdata;
    } sram_xbar_r_t;

    // SRAM Cntrl. <=> Scratchpad
    typedef struct packed {
        logic   valid;
        src_t         src;
        xbar_sram_w_t swz;
    } sram_w_port_req_t;

    typedef struct packed {
        logic valid;
        src_t src;
    } sram_w_port_res_t;

    typedef struct packed {
        logic valid;
        src_t       src;
        xbar_desc_t xbar;
    } sram_r_port_req_t;

    typedef struct packed {
        logic   valid;
        src_t         src;
        sram_xbar_r_t bank;
    } sram_r_port_res_t;

    // DRAM Cntrl. <=> Backend
    typedef struct packed {
        logicwrite;
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
    } sched_rsp_t;

    // ----------------------------------------------------------------------
    // Wires
    // ----------------------------------------------------------------------

    // Backend <=> DRAM Cntrl.
    logicbe_dram_req_valid;
    logicbe_dram_req_ready;
    dram_req_t be_dram_req;
    logicdram_be_res_valid;
    logicdram_be_res_ready;
    dram_res_t dram_be_res;

    // Scheduler <=> Backend 
    logic sched_req_valid [NUM_SCHED];
    logic sched_req_ready [NUM_SCHED];
    sched_req_t sched_req [NUM_SCHED];
    logic sched_rsp_valid [NUM_SCHED];
    sched_rsp_t sched_rsp [NUM_SCHED];

    // Frontend <=> Scratchpad channels
    // Read channels
    logic  fe_rd_req_valid [NUM_SCPADS];
    logic  fe_rd_req_ready [NUM_SCPADS];
    rd_req_t  fe_rd_req       [NUM_SCPADS];
    logic  fe_rd_res_valid [NUM_SCPADS];
    logic  fe_rd_res_ready [NUM_SCPADS];
    rd_res_t  fe_rd_res  [NUM_SCPADS];
    // Write channels
    logic  fe_wr_req_valid [NUM_SCPADS];
    logic  fe_wr_req_ready [NUM_SCPADS];
    wr_req_t  fe_wr_req       [NUM_SCPADS];
    logic  fe_wr_res_valid [NUM_SCPADS];
    logic  fe_wr_res_ready [NUM_SCPADS];
    wr_res_t  fe_wr_res  [NUM_SCPADS];

    // Backend <=>Scratchpad channels (arrays indexed by scratchpad)
    logic  be_rd_req_valid [NUM_SCPADS];
    logic  be_rd_req_ready [NUM_SCPADS];
    rd_req_t  be_rd_req       [NUM_SCPADS];
    logic  be_rd_res_valid [NUM_SCPADS];
    logic  be_rd_res_ready [NUM_SCPADS];
    rd_res_t  be_rd_res  [NUM_SCPADS];
    logic  be_wr_req_valid [NUM_SCPADS];
    logic  be_wr_req_ready [NUM_SCPADS];
    wr_req_t  be_wr_req       [NUM_SCPADS];
    logic  be_wr_res_valid [NUM_SCPADS];
    logic  be_wr_res_ready [NUM_SCPADS];
    wr_res_t  be_wr_res  [NUM_SCPADS];

    // Router <=>Scratchpad (per scratchpad arrays)
    // Head selections
    logic  spad_wr_sel_valid [NUM_SCPADS];
    logic  spad_wr_sel_ready [NUM_SCPADS];
    sel_wr_req_t spad_wr_sel_req   [NUM_SCPADS];
    logic  spad_rd_sel_valid [NUM_SCPADS];
    logic  spad_rd_sel_ready [NUM_SCPADS];
    sel_rd_req_t spad_rd_sel_req   [NUM_SCPADS];

    // Write path: input to W‑XBAR and output to SRAM
    logic   w_in_valid   [NUM_SCPADS];
    logic   w_in_ready   [NUM_SCPADS];
    xbar_desc_t   w_in_desc    [NUM_SCPADS];
    scpad_data_t  w_in_wdata   [NUM_SCPADS];
    xbar_sram_w_t w_to_sram    [NUM_SCPADS];
    sram_w_port_req_t spad_w_port_req [NUM_SCPADS];
    sram_w_port_res_t spad_w_port_res [NUM_SCPADS];

    // Read path: requests to SRAM and data from R‑XBAR
    sram_r_port_req_t spad_r_port_req [NUM_SCPADS];
    sram_r_port_res_t spad_r_port_res [NUM_SCPADS];
    logic  r_out_valid  [NUM_SCPADS];
    logic  r_out_ready  [NUM_SCPADS];
    sel_rd_res_t    r_out        [NUM_SCPADS];

    // Tail responses (per scratchpad)
    logic   spad_wr_resp_valid [NUM_SCPADS];
    logic   spad_wr_resp_ready [NUM_SCPADS];
    sel_wr_res_t  spad_wr_resp       [NUM_SCPADS];
    logic   spad_rd_resp_valid [NUM_SCPADS];
    logic   spad_rd_resp_ready [NUM_SCPADS];
    sel_rd_res_t  spad_rd_resp       [NUM_SCPADS];

    // ----------------------------------------------------------------------
    // Modport definitions
    // ----------------------------------------------------------------------

    // Scheduler <=> Backend
    modport sched_backend (
        output sched_req_valid, sched_req,
        input  sched_req_ready,
        input  sched_rsp_valid, sched_rsp
    );

    modport backend_sched (
        input  sched_req_valid, sched_req,
        output sched_req_ready,
        output sched_rsp_valid, sched_rsp
    );

    // Backend <=> Scratchpads
    modport backend (
        output be_rd_req_valid, be_rd_req, be_rd_res_ready,
        input  be_rd_req_ready, be_rd_res_valid, be_rd_res,
        output be_wr_req_valid, be_wr_req, be_wr_res_ready,
        input  be_wr_req_ready, be_wr_res_valid, be_wr_res
    );

    // Backend <=> DRAM
    modport backend_dram (
        output be_dram_req_valid, be_dram_req,
        input  be_dram_req_ready,
        input  dram_be_res_valid, dram_be_res,
        output dram_be_res_ready
    );

    modport dram (
        input  be_dram_req_valid, be_dram_req,
        output be_dram_req_ready,
        output dram_be_res_valid, dram_be_res,
        input  dram_be_res_ready
    );

    // Frontend <=> Scratchpads 
    modport frontend (
        output fe_rd_req_valid, fe_rd_req, fe_rd_res_ready,
        input  fe_rd_req_ready, fe_rd_res_valid, fe_rd_res,
        output fe_wr_req_valid, fe_wr_req, fe_wr_res_ready,
        input  fe_wr_req_ready, fe_wr_res_valid, fe_wr_res
    );

    // Head (Req MUX with BE>FE priority) per scratchpad
    modport spad_head (
        // Inputs: FE and BE requests/responses arrays
        input  fe_rd_req_valid, fe_rd_req, fe_rd_res_ready,
               fe_wr_req_valid, fe_wr_req, fe_wr_res_ready,
               be_rd_req_valid, be_rd_req, be_rd_res_ready,
               be_wr_req_valid, be_wr_req, be_wr_res_ready,
        // Outputs: ready signals back to FE and BE
        output fe_rd_req_ready, fe_wr_req_ready,
               be_rd_req_ready, be_wr_req_ready,
        // Selected outputs toward the path
        output spad_wr_sel_valid, spad_wr_sel_req,
               spad_rd_sel_valid, spad_rd_sel_req,
        input  spad_wr_sel_ready, spad_rd_sel_ready
    );

    // Tail (Resp Arb/Demux back to FE/BE) per scratchpad
    modport spad_tail (
        // Inputs from SRAM write ack and R‑XBAR 
        input  spad_wr_resp_valid, spad_wr_resp,
               spad_rd_resp_valid, spad_rd_resp,
        output spad_wr_resp_ready, spad_rd_resp_ready,
        // Outputs to FE and BE
        output fe_wr_res_valid, fe_wr_res,
               fe_rd_res_valid, fe_rd_res,
               be_wr_res_valid, be_wr_res,
               be_rd_res_valid, be_rd_res,
        input  fe_wr_res_ready, fe_rd_res_ready,
               be_wr_res_ready, be_rd_res_ready
    );

    // Write crossbars 
    modport xbar_w (
        input  w_in_valid, w_in_desc, w_in_wdata,
        output w_in_ready,
        output w_to_sram
    );

    // Read crossbars 
    modport xbar_r (
        input  spad_r_port_res,
        output r_out_valid, r_out,
        input  r_out_ready
    );

    // SRAM Controller
    modport sram_ctrl (
        input  spad_w_port_req, spad_r_port_req,
        output spad_w_port_res, spad_r_port_res
    );

    // Path glue between Head ↔ XBARs ↔ SRAM ctrl ↔ XBARs ↔ Tail
    modport spad_path (
        // Head-selected requests
        input  spad_wr_sel_valid, spad_wr_sel_req,
               spad_rd_sel_valid, spad_rd_sel_req,
        output spad_wr_sel_ready, spad_rd_sel_ready,
        // W-XBAR
        output w_in_valid, w_in_desc, w_in_wdata,
        input  w_in_ready, w_to_sram,
        // To/From SRAM controller
        output spad_w_port_req, spad_r_port_req,
        input  spad_w_port_res, spad_r_port_res,
        // R-XBAR
        input  r_out_valid, r_out,
        output r_out_ready,
        // To Tail
        output spad_wr_resp_valid, spad_wr_resp,
               spad_rd_resp_valid, spad_rd_resp,
        input  spad_wr_resp_ready, spad_rd_resp_ready
    );

    // ----------------------------------------------------------------------
    // Top-level modport
    // ----------------------------------------------------------------------
    modport top (
        // Scheduler ↔ Backend
        output sched_req_valid, sched_req,
        input  sched_req_ready,
        input  sched_rsp_valid, sched_rsp,
        // Backend ↔ DRAM
        output be_dram_req_valid, be_dram_req,
        input  be_dram_req_ready,
        input  dram_be_res_valid, dram_be_res,
        output dram_be_res_ready,
        // Frontend ↔ Scratchpad
        output fe_rd_req_valid, fe_rd_req, fe_rd_res_ready,
        input  fe_rd_req_ready, fe_rd_res_valid, fe_rd_res,
        output fe_wr_req_valid, fe_wr_req, fe_wr_res_ready,
        input  fe_wr_req_ready, fe_wr_res_valid, fe_wr_res,
        // Backend ↔ Scratchpad
        output be_rd_req_valid, be_rd_req, be_rd_res_ready,
        input  be_rd_req_ready, be_rd_res_valid, be_rd_res,
        output be_wr_req_valid, be_wr_req, be_wr_res_ready,
        input  be_wr_req_ready, be_wr_res_valid, be_wr_res
    );

endinterface

`endif 