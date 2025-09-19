`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface scpad_if;
    import scpad_types_pkg::*;

    ////////////////////////////////////////////////////////////////////////////

    // Refer to `scpad_types_pkg.vh` for the definition of scpad. 

    // Typical Control Flow within Scratchpad. 
    //      Ingress 
    //          Functional_Unit.SCPAD will pass DRAM Base Address to start loading from, num_rows and num_cols of the matrix (max bitwidth of both ports is 5)
    //          This information goes to Backend Prefetcher. 
    //              Backend Prefetcher has a FIFO containing {slot_mask, shift_mask, enable_mask}.
    //              It starts talking to the DRAM Controller by sending how many bytes to load (max 32, so bitwidth = 5). DRAM Controller signals when it's ready with the data. 
    //              When this signal goes high, Backend Prefetched will set crossbar reservation bit high. Only proceeds when the confirmation bit gets set high too. 
    //              Data is passed into through a `scpad_data wdata` field, and is routed into the crossbar along with the shift_mask and enable_mask. 
    //              Output from the crossbar is latched and held until SRAM is free. Remember, SRAM Control unit always loves Backend communication, unless it's already serving another request. 
    //              Here, the slot_mask is sent in, after which the final data is written into the banks. 
    //      Egress 
    //          From Scpad -> VReg           
    //              VReg Cntrl. is a part of Vector Core (VC). It will send in a request packet. Frontend Arbiter prioritizes the VC requests based on the valid bits of SA and VC request vectors. 
    //              It will send in an addr, valid, write (0/1). The Frontend VC will make a {slot_mask, shift_mask, enable_mask} pair, and set crossbar reservation bit high. It will only proceed if the
    //               confimation bit gets set high too
    //              slot_mask and a read signal gets sent into SRAM Cntrl, and then `scpad_data rdata` is read out. 
    //              This gets routed into the crossbar, along with the shift_mask and enable_mask. 
    //              Output of crossbar gets set into the rdata going out through the response packet in the common bus shared by VC and SA, only that valid bits differ. 
    //          From Scpad -> SA 
    //              TCA handles this communication in the same way the VReg. Cntrl. is expected to. 

    // Arbitration Logic for the SRAM Control itself. 
    //      Always prioritize Backend, then Frontend VC, then Frontend SA

    ////////////////////////////////////////////////////////////////////////////

    // Crossbar Signals
    typedef struct packed {
        slot_mask   slot;
        shift_mask  shift;
        enable_mask  valid;
    } xbar_desc_t;

    typedef struct packed {
        logic      valid;
        xbar_desc_t desc;
        scpad_data  in;
    } xbar_w_req_t;

    typedef struct packed {
        logic      valid;
        xbar_desc_t desc;
    } xbar_r_req_t;

    xbar_desc_t vc_xbar_desc, sa_xbar_desc, be_xbar_desc;
    xbar_w_req_t be_xbar_req;         
    xbar_r_req_t vc_xbar_req, sa_xbar_req; 
    logic        vc_xbar_res, sa_xbar_res, be_xbar_res;
    scpad_data   xbar_out_egress;

    // SRAM Control <-> Goes to TCA and VReg Ctrl.
    typedef struct packed {
        logic valid;
        slot_mask  slot_mask;
        enable_mask enable_mask; 
        scpad_data wdata;
    } sram_req_t;

    typedef struct packed {
        logic valid;
        scpad_data rdata;
    } sram_res_t;

    // Split the *frontend* channel into VC and SA to avoid multi-drivers
    sram_req_t vc_sram_banks_req, sa_sram_banks_req;
    sram_res_t vc_sram_banks_res, sa_sram_banks_res;

    sram_req_t backend_sram_banks_req;
    sram_res_t backend_sram_banks_res;

    scpad_data sram_banks_write_vector, sram_banks_read_vector;

    // Frontend requests + responses (unchanged structs)
    // Systolic Array Request -> Comes from the TCA
    // Vector Core Request -> Comes from the VReg Ctrl.
    //      Frontend Arbitration logic will use req_t.valid vs req_t.valid to decide which gets served first. 
    typedef struct packed { 
        logic valid; 
        logic write; // if valid and !write -> then its a read
        logic [SCPAD_ADDR_WIDTH-1:0] addr; // always the BASE row, basically an identifier
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
        logic [MAX_DIM_WIDTH-1:0] row_id, col_id; // used by VC and SA -> tells us which row or which tile
        logic row_or_col; // 0 to load a row, 1 to load a col | set by VC or SA
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load from
        scpad_data wdata; 
    } frontend_req_t; 


    typedef struct packed {
        logic      valid;
        logic      complete;
        scpad_data rdata;
    } frontend_res_t;

    frontend_req_t tca_frontend_req, vc_frontend_req;
    frontend_res_t frontend_tca_res, frontend_vc_res;

    // Scheduler Request; Functional_Unit.SCPAD -> Backend
    typedef struct packed { 
        logic valid; 
        logic write; 
        logic [SCPAD_ADDR_WIDTH-1:0] addr; // always the BASE row, basically an identifier
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
        logic [MAX_DIM_WIDTH-1:0] row_id, col_id; // used by VC and SA -> tells us which row or which tile
        logic row_or_col; // 0 to load a row, 1 to load a col | set by VC or SA
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load from
    } scheduler_req_t; 

    typedef struct packed { 
        logic valid; 
        logic complete; 
    } scheduler_res_t;

    scheduler_req_t scheduler_backend_req;
    scheduler_res_t backend_scheduler_res;

    // DRAM Request from Scratchpad
    typedef struct packed { 
        logic valid; 
        logic [DRAM_ADDR_WIDTH-1:0] dram_addr; 
        logic [COL_IDX_WIDTH-1:0] num_bytes; 
    } dram_req_t;

    typedef struct packed { 
        logic valid; 
        logic complete; 
        scpad_data rdata; 
    } dram_res_t;

    dram_req_t backend_dram_req;
    dram_res_t dram_backend_res;


    ////////////////////////////////////////////////////////////////////////////

    // Scratchpad will talk to DRAM Controller, Vector Core, Systolic Array and Functional_Unit.SCPAD. 
    modport top (
        input  tca_frontend_req, vc_frontend_req, scheduler_backend_req, dram_backend_res,
        output frontend_tca_res,  frontend_vc_res,  backend_scheduler_res, backend_dram_req
    );


    // Backend Prefetcher will talk to the SRAM Control, Crossbar, DRAM Controller, Vector Core and Systolic Array
    // Responsible for all ingress
    modport backend (
        input  scheduler_backend_req,
        input  be_xbar_res,
        output be_xbar_req,
        input  dram_backend_res,
        output backend_dram_req,
        output sram_banks_write_vector,
        // backend sram
        output backend_sram_banks_req,
        input  backend_sram_banks_res
    );

    modport fu (
        input  backend_scheduler_res,
        output scheduler_backend_req
    );

    // A single "frontend" that arbitrates VC vs SA at packet level is fine,
    // but we give VC and SA their own SRAM channels to avoid multi-drive.
    modport frontend (
        input  tca_frontend_req, vc_frontend_req, xbar_out_egress,
        output frontend_tca_res, frontend_vc_res
    );

    modport frontend_vc (
        input  vc_frontend_req,
        output frontend_vc_res,

        input  vc_sram_banks_res,
        output vc_sram_banks_req,

        input  vc_xbar_res, xbar_out_egress,
        output vc_xbar_req, vc_xbar_desc
    );

    modport frontend_sa (
        input  tca_frontend_req,
        output frontend_tca_res,

        input  sa_sram_banks_res,
        output sa_sram_banks_req,

        input  sa_xbar_res, xbar_out_egress,
        output sa_xbar_req, sa_xbar_desc
    );

    modport crossbar (
        input  vc_xbar_desc, sa_xbar_desc, be_xbar_desc,
        input  be_xbar_req, vc_xbar_req, sa_xbar_req,

        output vc_xbar_res, sa_xbar_res, be_xbar_res,
        output xbar_out_egress
    );


    modport sram_ctrl (
        input  frontend_sram_banks_req,
        input  backend_sram_banks_req,
        input  sram_banks_write_vector,

        output frontend_sram_banks_res,
        output backend_sram_banks_res,
        output sram_banks_read_vector
    );

endinterface
`endif
