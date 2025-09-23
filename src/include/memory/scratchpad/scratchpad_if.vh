/*
  Akshath Raghav Ravikiran
  araviki@purdue.edu

  Scratchpad Interface V3
*/

`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface scpad_if;
    import scpad_types_pkg::*;

    ////////////////////////////////////////////////////////////////////////////

    // Refer to `scpad_types_pkg.vh` for the parameters. 
    // Below, we go through the typical workflow of Scratchpad Operations. 

    ////////////////////////////////////////////////////////////////////////////

    typedef enum logic [1:0] {
        FRONTEND_VC_REQ = 2'b00, 
        FRONTEND_SA_REQ = 2'b01, 
        BACKEND_REQ = 2'b10, 
    } sram_interaction_id_t;

    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////// Crossbar + SRAM Banks //////////////////////
    ///////////////////////////////////////////////////////////////////////////

    // We have one set of structs defining a request from the Frontend and Backend POV
    // We have another set of structs defining the way the requests are ARB and propogated through xbar
    // We have one final set of structs defining only the required ports to go into the SRAM banks

    // Most of this looks overengineered, but will very easily simplify during synthesis. 

    typedef struct packed {
        slot_mask   slot_mask;
        shift_mask  shift_mask;
        enable_mask  valid_mask;
    } xbar_desc_t;

    typedef struct packed {
        sram_interaction_id_t int_id; 
        logic valid;
        xbar_desc_t xbar_desc; 
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to read from
    } sram_r_req_t;

    typedef struct packed {
        sram_interaction_id_t int_id; 
        logic valid;
        scpad_data rdata;
    } sram_r_res_t;

    typedef struct packed {
        sram_interaction_id_t int_id; 
        logic valid;
        xbar_desc_t xbar_desc; 
        scpad_data wdata;
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to write to
    } sram_w_req_t;

    typedef struct packed {
        sram_interaction_id_t int_id; 
        logic valid;
    } sram_w_res_t;

    typedef struct packed {
        logic  valid;
        sram_interaction_id_t int_id;
        logic [NUM_COLS-1:0]  mask;    
    } inflight_tag_t;

    typedef struct packed {
        logic valid;
        slot_mask  slot_mask;
        enable_mask valid_mask;
        scpad_data_t wdata;
    } xbar_sram_w_t;

    // Backpressure. 
    logic sram_busy; 

    // Read goes directly to the SRAM Control which ARBs. 
    sram_r_req_t vc_sram_r_banks_req, sa_sram_r_banks_req, backend_sram_r_banks_req, sram_read_req;
    sram_r_res_t vc_sram_r_banks_res, sa_sram_r_banks_res, backend_sram_r_banks_res, sram_read_res; 

    // Writes get ARBs before they go into the Write Crossbar. 
    sram_w_req_t vc_sram_w_banks_req, sa_sram_w_banks_req, backend_sram_w_banks_req, sram_write_req; 
    sram_w_res_t vc_sram_w_banks_res, sa_sram_w_banks_res, backend_sram_w_banks_res, sram_write_res; 

    // Then, we directly MUX out at the same done cycle. 
    xbar_sram_w_t xbar_sram_w; // write_crossbar -> sram
    sram_xbar_r_t sram_xbar_r; 

    ////////////////////////////////////////////////////////////////////////////
    /////////////////////// Frontend Internal + External //////////////////////
    ///////////////////////////////////////////////////////////////////////////

    typedef struct packed { 
        logic valid; 
        logic write; // if valid and !write -> then its a read
        logic [SCPAD_ADDR_WIDTH-1:0] addr; // starting address of the tile
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
        logic [MAX_DIM_WIDTH-1:0] row_id, col_id; // used by VC and SA -> tells us which row or which tile
        logic row_or_col; // 0 to load a row, 1 to load a col | set by VC or SA
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load from
        scpad_data wdata; 
    } frontend_req_t; 

    typedef struct packed {
        logic valid;
        logic complete;
        scpad_data rdata;
    } frontend_res_t;

    frontend_req_t tca_frontend_req, vc_frontend_req;
    frontend_res_t frontend_tca_res, frontend_vc_res;
    scpad_data_t frontend_xbar_data, xbar_frontend_data; // post-MUX

    ////////////////////////////////////////////////////////////////////////////
    /////////////////////// Backend Internal + External //////////////////////
    ///////////////////////////////////////////////////////////////////////////

    typedef struct packed { 
        logic valid; 
        logic write; 
        logic [SCPAD_ADDR_WIDTH-1:0] addr; // always the BASE row, basically an identifier
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load to
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
        scpad_data wdata; 
    } dram_req_t;

    typedef struct packed { 
        logic valid; 
        logic complete; 
        scpad_data rdata; 
    } dram_res_t;

    dram_req_t backend_dram_req;
    dram_res_t dram_backend_res;


    ////////////////////////////////////////////////////////////////////////////
    /////////////////// External Modports to other Teams //////////////////////
    ///////////////////////////////////////////////////////////////////////////

    // Scheduler: @JayShah
    // DRAM: @AryanKadakia, @TriThan
    // TCA: @SaandiyaM, @Nikhil 
    // VC: @JosephG, @ChaseJ
    modport top ( 
        input  tca_frontend_req, vc_frontend_req, scheduler_backend_req, dram_backend_res,
        output frontend_tca_res,  frontend_vc_res,  backend_scheduler_res, backend_dram_req
    );

    modport dram ( // @AryanKadakia, @TriThan
        output dram_backend_res, 
        input backend_dram_req
    ); 

    modport tca ( //  @SaandiyaM, @Nikhil 
        output tca_frontend_req, 
        input frontend_tca_res
    );


    modport vc ( //  @JosephG, @ChaseJ
        output vc_frontend_req, 
        input frontend_vc_res
    );

    modport scheduler_fu ( // @JayShah
        output scheduler_backend_req
        input  backend_scheduler_res
    );

    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////// Internal Modports //////////////////////////
    ///////////////////////////////////////////////////////////////////////////

    modport backend (
        input sram_busy,

        input scheduler_backend_req,
        output backend_scheduler_res, 

        input  backend_sram_r_banks_res, backend_sram_w_banks_res,
        output backend_sram_r_banks_req, backend_sram_w_banks_req, 

        input  dram_backend_res,
        output backend_dram_req,
    );

    modport frontend (
        input sram_busy,

        input tca_read_complete, vc_read_complete, 
        output frontend_ready, 

        input tca_frontend_req, vc_frontend_req, 
        output frontend_tca_res, frontend_vc_res, 

        input frontend_sram_read_res, frontend_sram_write_res
        output frontend_sram_read_req, frontend_sram_write_req
    );

    modport frontend_vc (
        input vc_frontend_req,
        output frontend_vc_res,

        input  vc_sram_r_banks_res, vc_sram_w_banks_res,
        output vc_sram_r_banks_req, vc_sram_w_banks_req
    );

    modport frontend_sa (
        input sa_frontend_req,
        output frontend_sa_res,

        input  sa_sram_r_banks_res, sa_sram_w_banks_res,
        output sa_sram_r_banks_req, sa_sram_w_banks_req
    );

    modport read_xbar (
        input  vc_sram_r_banks_req, sa_sram_r_banks_req, backend_sram_r_banks_req, sram_xbar_r, 
        output vc_sram_r_banks_res, sa_sram_r_banks_res, backend_sram_r_banks_res, xbar_sram_r
    );

    modport write_xbar (
        input  vc_sram_w_banks_req, sa_sram_w_banks_req, backend_sram_w_banks_req,
        output xbar_sram_w
    );

    modport sram_ctrl (
        input sram_read_req, sram_write_req,
        output sram_read_res, sram_write_res 
    );

endinterface
`endif
