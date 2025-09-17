`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface spad_if;
    import spad_types_pkg::*;

    // Refer to `scpad_types_pkg.vh` for the definition of scpad. 

    // Typical Control Flow within Scratchpad. 
    //      Ingress 
    //          Functional_Unit.SCPAD will pass DRAM Base Address to start loading from, num_rows and num_cols of the matrix (max bitwidth of both ports is 5)
    //          This information goes to Backend Prefetcher. 
    //              Backend Prefetcher has a FIFO containing {slot_mask, shift_mask, valid_mask}.
    //              It starts talking to the DRAM Controller by sending how many bytes to load (max 32, so bitwidth = 5). DRAM Controller signals when it's ready with the data. 
    //              When this signal goes high, Backend Prefetched will set crossbar reservation bit high. Only proceeds when the confirmation bit gets set high too. 
    //              Data is passed into through a `scpad_data wdata` field, and is routed into the crossbar along with the shift_mask and valid_mask. 
    //              Output from the crossbar is latched and held until SRAM is free. Remember, SRAM Control unit always loves Backend communication, unless it's already serving another request. 
    //              Here, the slot_mask is sent in, after which the final data is written into the banks. 
    //      Egress 
    //          From Scpad -> VReg           
    //              VReg Cntrl. is a part of Vector Core (VC). It will send in a request packet. Frontend Arbiter prioritizes the VC requests based on the valid bits of SA and VC request vectors. 
    //              It will send in an addr, valid, write (0/1). The Frontend VC will make a {slot_mask, shift_mask, valid_mask} pair, and set crossbar reservation bit high. It will only proceed if the
    //               confimation bit gets set high too
    //              slot_mask and a read signal gets sent into SRAM Cntrl, and then `scpad_data rdata` is read out. 
    //              This gets routed into the crossbar, along with the shift_mask and valid_mask. 
    //              Output of crossbar gets set into the rdata going out through the response packet in the common bus shared by VC and SA, only that valid bits differ. 
    //          From Scpad -> SA 
    //              TCA handles this communication in the same way the VReg. Cntrl. is expected to. 

    // Arbitration Logic for the SRAM Control itself. 
    //      Always prioritize Backend, then Frontend VC, then Frontend SA

    // Crossbar Signals
    typedef struct packed {
        slot_mask  slot;
        shift_mask  shift;
        valid_mask  valid;
    } xbar_desc_t;
    xbar_desc_t vc_xbar_desc, sa_xbar_desc, be_xbar_desc; 
    logic crossbar_req_vc, crossbar_req_sa, crossbar_req_be; // request into the crossbar arb. logic
    logic crossbar_reserved_vc, crossbar_reserved_sa, crossbar_reserved_be; // confirms if it's reserved or not for either BE, FE VC, FE SA
    scpad_data xbar_in_vc, xbar_in_sa, xbar_in_be;
    scpad_data xbar_out;

    // SRAM Control -> Goes to TCA and VReg Ctrl.
    typedef struct packed {
        logic [1:0]  valid; // [1]=VC, [0]=SA
        logic  ready;
        scpad_data rdata; 
    } resp_t;

    logic sram_req_be, sram_req_sa, sram_req_vc; 
    logic sram_reserved_be, sram_reserved_vc, sram_reserved_sa; 
    resp_t resp;

    // Systolic Array Request -> Comes from the TCA
    // Vector Core Request -> Comes from the VReg Ctrl.
    //      Frontend Arbitration logic will use req_sa_t.valid vs req_vc_t.valid to decide which gets served first. 
    typedef struct packed { 
        logic valid; 
        logic write; // if valid and !write -> then its a read
        logic [SCPAD_ADDR_WIDTH-1:0] addr; // always the BASE row, basically an identifier
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
        logic [MAX_DIM_WIDTH-1:0] row_id, col_id; // used by VC and SA -> tells us which row or which tile
        logic row_or_col; // 0 to load a row, 1 to load a col | set by VC or SA
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load from
        scpad_data wdata; 
    } req_sa_t, req_vc_t; 

    // Scheduler Request -> Functional_Unit.SCPAD
    typedef struct packed { 
        logic valid; 
        logic write; 
        logic [SCPAD_ADDR_WIDTH-1:0] addr; // always the BASE row, basically an identifier
        logic [MAX_DIM_WIDTH-1:0] num_rows, num_cols; // purely for sysarray.ld -> loading an entire tile/kernel into the SA
        logic [MAX_DIM_WIDTH-1:0] row_id, col_id; // used by VC and SA -> tells us which row or which tile
        logic row_or_col; // 0 to load a row, 1 to load a col | set by VC or SA
        logic [SCPAD_ID_WIDTH-1:0] scpad_id; // which scpad to load from
    } req_be_t; 

    req_sa_t sa_req;
    req_vc_t vc_req;
    req_be_t be_req; 

    // Scratchpad will talk to DRAM Controller, Vector Core, Systolic Array and Functional_Unit.SCPAD. 
    modport external (
        output sa_req, vc_req, be_req, 
        input  resp  
    );

    // Backend Prefetcher will talk to the SRAM Control, Crossbar, DRAM Controller, Vector Core and Systolic Array
    // Responsible for all ingress
    modport backend (
        input  be_req, 
        input  resp, 
        output be_xbar_desc, crossbar_req_be, 
        output xbar_in_be,
        output sram_req_be
    );


    // Frontend VC will talk to the SRAM Control and Crossbar and have output ports into Vector Core
    // Responsible for purely VC Egress
    modport frontend_vc (
        input  vc_req,
        input  resp,   
        output vc_xbar_desc, crossbar_req_vc, crossbar_reserved_vc, 
        output sram_req_vc
    );


    // Frontend SA will talk to the SRAM Control and Crossbar and have output ports into Systolic Array
    // Responsible for purely SA Egress
    modport frontend_sa (
        input  sa_req, 
        input  resp,  
        output sa_xbar_desc, crossbar_req_sa, crossbar_reserved_sa, 
        output sram_req_sa
    );

    modport crossbar (
        input  crossbar_req_vc, vc_xbar_desc, xbar_in_vc,
            crossbar_req_sa, sa_xbar_desc, xbar_in_sa,
            crossbar_req_be, be_xbar_desc,  xbar_in_be,
        output crossbar_reserved_vc, crossbar_reserved_sa, crossbar_reserved_be, 
        output xbar_out
    );

    modport sram_ctrl (
        input  sram_req_be, sram_req_vc, sram_req_sa,  // highlights the intent of each unit
        output sram_reserved_be, sram_reserved_vc, sram_reserved_sa, // confirms that it's ready 

        input be_xbar_desc, sa_xbar_desc, vc_xbar_desc, 

        input  xbar_out,    
        output xbar_in_vc,     
        output xbar_in_sa,  

        output resp // drives respective .valid bit         
    );


endinterface

`endif
