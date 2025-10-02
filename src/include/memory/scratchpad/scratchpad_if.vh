/*
  Akshath Raghav Ravikiran
  araviki@purdue.edu

  Scratchpad Interface V3 (fixed)
*/

`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface scpad_if;
    import scpad_types_pkg::*; // make sure scpad_types_pkg is compiled first

    // for some reason vlog was complaining about typedefs not being on scpad_types_pkg, moved it to there.
    // ////////////////////////////////////////////////////////////////////////////
    // // Interaction ID
    // typedef enum logic [1:0] {
    //     FRONTEND_VC1_REQ = 2'b00,
    //     FRONTEND_VC2_REQ = 2'b01,
    //     BACKEND_REQ      = 2'b10
    // } sram_interaction_id_t;

    // ////////////////////////////////////////////////////////////////////////////
    // // Crossbar descriptor
    // // These element types (slot_mask_t, shift_mask_t, enable_mask_t, scpad_data_t)
    // // must be defined in scpad_types_pkg. If different names used there, adapt.
    // typedef struct packed {
    //     slot_mask_t   slot_mask;
    //     shift_mask_t  shift_mask;
    //     enable_mask_t valid_mask;
    // } xbar_desc_t;

    // // SRAM read/write request/response structs
    // typedef struct packed {
    //     sram_interaction_id_t int_id;
    //     logic valid;
    //     xbar_desc_t xbar_desc;
    //     logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    // } sram_r_req_t;

    // typedef struct packed {
    //     sram_interaction_id_t int_id;
    //     logic valid;
    //     scpad_data_t rdata;
    // } sram_r_res_t;

    // typedef struct packed {
    //     sram_interaction_id_t int_id;
    //     logic valid;
    //     xbar_desc_t xbar_desc;
    //     scpad_data_t wdata;
    //     logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    // } sram_w_req_t;

    // typedef struct packed {
    //     sram_interaction_id_t int_id;
    //     logic valid;
    // } sram_w_res_t;

    // typedef struct packed {
    //     logic  valid;
    //     sram_interaction_id_t int_id;
    //     logic [NUM_COLS-1:0] mask;
    // } inflight_tag_t;

    // typedef struct packed {
    //     logic valid;
    //     slot_mask_t  slot_mask;
    //     enable_mask_t valid_mask;
    //     scpad_data_t wdata;
    // } xbar_sram_w_t;

    // // Use existing r/w types as alias for xbar routing if needed
    // typedef sram_r_res_t sram_xbar_r_t;

    // Backpressure. 
    logic sram_busy; 

    // Read goes directly to the SRAM Control which ARBs. 
    sram_r_req_t vc_sram_r_banks_req, sa_sram_r_banks_req, backend_sram_r_banks_req, sram_read_req;
    sram_r_res_t vc_sram_r_banks_res, sa_sram_r_banks_res, backend_sram_r_banks_res, sram_read_res;

    // Writes get ARBs before they go into the Write Crossbar. 
    sram_w_req_t vc_sram_w_banks_req, sa_sram_w_banks_req, backend_sram_w_banks_req, sram_write_req;
    sram_w_res_t vc_sram_w_banks_res, sa_sram_w_banks_res, backend_sram_w_banks_res, sram_write_res;

    // Then, we directly MUX out at the same done cycle. 
    xbar_sram_w_t xbar_sram_w;
    sram_xbar_r_t sram_xbar_r;

    // ////////////////////////////////////////////////////////////////////////////
    // // Frontend request / response types (per-VC)
    // typedef struct packed {
    //     logic valid;
    //     logic write;
    //     logic [SCPAD_ADDR_WIDTH-1:0] addr;
    //     logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols;
    //     logic [MAX_DIM_WIDTH-1:0] row_id, col_id;
    //     logic row_or_col;
    //     logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    //     scpad_data_t wdata;
    // } frontend_req_t;

    // typedef struct packed {
    //     logic valid;
    //     logic complete;
    //     scpad_data_t rdata;
    // } frontend_res_t;

    // Two VC frontends
    frontend_req_t vc1_frontend_req, vc2_frontend_req;
    frontend_res_t frontend_vc1_res, frontend_vc2_res;

    // crossbar data lines
    scpad_data_t frontend_xbar_data, xbar_frontend_data;

    // ////////////////////////////////////////////////////////////////////////////
    // // Backend / DRAM request/res
    // typedef struct packed {
    //     logic valid;
    //     logic write;
    //     logic [SCPAD_ADDR_WIDTH-1:0] addr;
    //     logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols;
    //     logic [SCPAD_ID_WIDTH-1:0] scpad_id;
    // } scheduler_req_t;

    // typedef struct packed {
    //     logic valid;
    //     logic complete;
    // } scheduler_res_t;

    scheduler_req_t scheduler_backend_req;
    scheduler_res_t backend_scheduler_res;

    // typedef struct packed {
    //     logic valid;
    //     logic write;
    //     logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //     logic [COL_IDX_WIDTH-1:0] num_bytes;
    //     scpad_data_t wdata;
    // } dram_req_t;

    // typedef struct packed {
    //     logic valid;
    //     logic complete;
    //     scpad_data_t rdata;
    // } dram_res_t;

    dram_req_t backend_dram_req;
    dram_res_t dram_backend_res;

    ////////////////////////////////////////////////////////////////////////////
    // Per-VC read-complete signals and per-VC sram-bank request/res that
    // were referenced in modports but not previously declared.
    logic vc1_read_complete, vc2_read_complete;
    logic frontend_ready;

    // Frontend <-> SRAM controller handshake (per-frontend)
    sram_r_res_t frontend_sram_read_res;
    sram_w_res_t frontend_sram_write_res;
    sram_r_req_t frontend_sram_read_req;
    sram_w_req_t frontend_sram_write_req;

    // Per-VC read & write bank-level request/res signals (rename consistent with modports)
    sram_r_req_t vc1_sram_r_banks_req, vc2_sram_r_banks_req;
    sram_r_res_t vc1_sram_r_banks_res, vc2_sram_r_banks_res;
    sram_w_req_t vc1_sram_w_banks_req, vc2_sram_w_banks_req;
    sram_w_res_t vc1_sram_w_banks_res, vc2_sram_w_banks_res;

    ////////////////////////////////////////////////////////////////////////////
    /////////////////// External Modports to other Teams ///////////////////////
    ////////////////////////////////////////////////////////////////////////////
    modport top (
        input  vc1_frontend_req, vc2_frontend_req, scheduler_backend_req, dram_backend_res,
        output frontend_vc1_res, frontend_vc2_res, backend_scheduler_res, backend_dram_req
    );

    modport dram (
        output dram_backend_res,
        input backend_dram_req
    );

    modport vc1 (
        output vc1_frontend_req,
        input  frontend_vc1_res
    );

    modport vc2 (
        output vc2_frontend_req,
        input  frontend_vc2_res
    );

    modport scheduler_fu (
        output scheduler_backend_req,
        input  backend_scheduler_res
    );

    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////// Internal Modports ///////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    modport backend (
        input sram_busy,

        input scheduler_backend_req,
        output backend_scheduler_res,

        input backend_sram_r_banks_res, backend_sram_w_banks_res,
        output backend_sram_r_banks_req, backend_sram_w_banks_req,

        input dram_backend_res,
        output backend_dram_req
    );

    // Single frontend view: both VC1 & VC2 appear as inputs; responses are outputs.
    modport frontend (
        input sram_busy,

        input vc1_read_complete, vc2_read_complete,
        output frontend_ready,

        input vc1_frontend_req, vc2_frontend_req,
        output frontend_vc1_res, frontend_vc2_res,

        input frontend_sram_read_res, frontend_sram_write_res,
        output frontend_sram_read_req, frontend_sram_write_req
    );

    // VC-specific modports for instantiating one-FSM-per-VC
    modport frontend_vc1 (
        input vc1_frontend_req,
        output frontend_vc1_res,

        input  vc1_sram_r_banks_res, vc1_sram_w_banks_res,
        output vc1_sram_r_banks_req, vc1_sram_w_banks_req
    );

    modport frontend_vc2 (
        input vc2_frontend_req,
        output frontend_vc2_res,

        input  vc2_sram_r_banks_res, vc2_sram_w_banks_res,
        output vc2_sram_r_banks_req, vc2_sram_w_banks_req
    );

    // Crossbar read/write ports
    modport read_xbar (
        input  vc1_sram_r_banks_req, vc2_sram_r_banks_req, backend_sram_r_banks_req, sram_xbar_r,
        output vc1_sram_r_banks_res, vc2_sram_r_banks_res, backend_sram_r_banks_res, xbar_sram_w // was xbar_sram_r, idk if it was a typo
    );

    modport write_xbar (
        input  vc1_sram_w_banks_req, vc2_sram_w_banks_req, backend_sram_w_banks_req,
        output xbar_sram_w
    );

    // sram controller modport
    modport sram_ctrl (
        input sram_read_req, sram_write_req,
        output sram_read_res, sram_write_res
    );

    // generic alias signals (default hook up to VC1 for now)
    frontend_req_t frontend_req;
    frontend_res_t frontend_res;
    logic read_complete;

    // default assignment (later parameterize/replicate for VC2)
    assign frontend_req    = vc1_frontend_req;
    assign frontend_res    = frontend_vc1_res;
    assign read_complete   = vc1_read_complete;

    // generic modport for r_fsm
    modport vc_frontend (
        input  frontend_req,
        output frontend_res,
        input  read_complete,
        input  sram_busy,
        output frontend_ready,
        input  frontend_sram_read_res,
        input  frontend_sram_write_res,
        output frontend_sram_read_req,
        output frontend_sram_write_req
    );


endinterface
`endif
