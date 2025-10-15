/*
  Akshath Raghav Ravikiran
  araviki@purdue.edu

  Scratchpad Interface V3
*/

`ifndef SCPAD_IF_VH
`define SCPAD_IF_VH

interface scpad_if;
    import spad_types_pkg::*; 

    // ==========================================================================
    // ============================ DATA STRUCTURES =============================
    // ==========================================================================


    // --------------------------
    // Crossbar descriptors
    // --------------------------
        typedef struct packed {
            slot_mask_t    slot_mask; // per-col row/slot indices feeding banks
            shift_mask_t   shift_mask; // per-col shift/bank mapping
            enable_mask_t  valid_mask;  // per-col enable/valid
        } xbar_desc_t;

    // --------------------------
    // FE/BE-side structs
    // --------------------------
        typedef struct packed {
            logic [SCPAD_ADDR_WIDTH-1:0] addr;
            logic [MAX_DIM_WIDTH-1:0]    num_rows;
            logic [MAX_DIM_WIDTH-1:0]    num_cols;
            logic [MAX_DIM_WIDTH-1:0]    row_id;
            logic [MAX_DIM_WIDTH-1:0]    col_id;
            logic row_or_col; 
            xbar_desc_t  xbar;    
        } rd_req_t;

        typedef struct packed {
            logic  complete;  
            scpad_data_t   rdata;    
        } rd_res_t;

        typedef struct packed {
            logic [SCPAD_ADDR_WIDTH-1:0] addr;
            logic [MAX_DIM_WIDTH-1:0]    num_rows;
            logic [MAX_DIM_WIDTH-1:0]    num_cols;
            logic [MAX_DIM_WIDTH-1:0]    row_id;
            logic [MAX_DIM_WIDTH-1:0]    col_id;
            logic row_or_col;
            xbar_desc_t  xbar;       
            scpad_data_t wdata;    
        } wr_req_t;

        typedef struct packed {
            logic complete;         
        } wr_res_t;

    // --------------------------
    // After Router BE>FE 
    // --------------------------
        typedef struct packed {
            src_t    src;         
            xbar_desc_t  xbar;
            scpad_data_t wdata;       
        } sel_wr_req_t;

        typedef struct packed {
            src_t src;
        } sel_wr_res_t;

        typedef struct packed {
            src_t  src;
            xbar_desc_t xbar;        
        } sel_rd_req_t;

        typedef struct packed {
            src_t src;
            scpad_data_t rdata;
        } sel_rd_res_t;

    // --------------------------
    // Crossbar-side structs
    // W-XBAR output toward SRAM, R-XBAR input from SRAM
    // --------------------------
        typedef struct packed {
            logic   valid;
            enable_mask_t  valid_mask;
            slot_mask_t   slot_mask;
            scpad_data_t wdata;
        } xbar_sram_w_t; // swizzled write beats to SRAM ctrl (pre-bank)

        typedef struct packed {
            logic   valid;
            enable_mask_t  valid_mask;
            shift_mask_t   shift_mask;
            scpad_data_t   rdata;
        } sram_xbar_r_t; // raw bank data+ctrl from SRAM ctrl (post-bank)

    // --------------------------
    // SRAM-controller logical ports per SCPAD
    // - Write path receives swizzled beats (xbar_sram_w_t) + origin tag
    // - Read path receives request ctrl (xbar_desc) and returns raw bank beats
    // --------------------------
        typedef struct packed {
            logic  valid;
            src_t         src;
            xbar_sram_w_t swz;    
        } sram_w_port_req_t;

        typedef struct packed {
            logic valid;
            src_t src;
        } sram_w_port_res_t;

        typedef struct packed {
            logic       valid;
            src_t       src;
            xbar_desc_t xbar;     
        } sram_r_port_req_t;

        typedef struct packed {
            logic  valid;
            src_t         src;
            sram_xbar_r_t bank;   
        } sram_r_port_res_t;

    // --------------------------
    // DRAM controller <=> Backend
    // --------------------------
        typedef struct packed {
            logic       write;     
            logic [DRAM_ID_WIDTH-1:0]   id;         
            logic [DRAM_ADDR_WIDTH-1:0] dram_addr; 
            logic [COL_IDX_WIDTH-1:0]   num_bytes; 
            scpad_data_t                wdata;    
        } dram_req_t;

        typedef struct packed {
            logic       valid;     
            logic [DRAM_ID_WIDTH-1:0]   id;         
            logic [DRAM_ADDR_WIDTH-1:0] dram_addr; 
            logic [COL_IDX_WIDTH-1:0]   num_bytes;  
        } dram_read_req_t;

        typedef struct packed {
            logic     complete;     
            logic [DRAM_ID_WIDTH-1:0] id;           // echoes request tag
            scpad_data_t              rdata;      
        } dram_res_t;

        typedef struct packed {
            logic write;
            logic [SCPAD_ADDR_WIDTH-1:0] spad_addr;
            logic [MAX_DIM_WIDTH-1:0]    num_rows;
            logic [MAX_DIM_WIDTH-1:0]    num_cols;
            logic [MAX_DIM_WIDTH-1:0]    row_id;
            logic [MAX_DIM_WIDTH-1:0]    col_id;
            logic row_or_col;         
            logic [SCPAD_ID_WIDTH-1:0]   scpad_id;             
        } sched_req_t;

        typedef struct packed {
            logic accepted;
        } sched_rsp_t;

    // ==========================================================================
    // ========================== SIGNALS / CHANNELS ============================
    // ==========================================================================

    // --------------------------
    // Backend <=> DRAM controller
    // --------------------------
        logic      be_dram_req_valid, be_dram_req_ready;
        dram_req_t be_dram_req;

        logic      dram_be_res_valid, dram_be_res_ready;
        dram_res_t dram_be_res;

    // --------------------------
    // FE0 <=> SCPAD0
    // --------------------------
        logic   fe0_rd_req_valid, fe0_rd_req_ready;
        rd_req_t fe0_rd_req;
        logic   fe0_rd_res_valid, fe0_rd_res_ready;
        rd_res_t fe0_rd_res;

        logic   fe0_wr_req_valid, fe0_wr_req_ready;
        wr_req_t fe0_wr_req;
        logic   fe0_wr_res_valid, fe0_wr_res_ready;
        wr_res_t fe0_wr_res;

    // --------------------------
    // FE1 <=> SCPAD1
    // --------------------------
        logic   fe1_rd_req_valid, fe1_rd_req_ready;
        rd_req_t fe1_rd_req;
        logic   fe1_rd_res_valid, fe1_rd_res_ready;
        rd_res_t fe1_rd_res;

        logic   fe1_wr_req_valid, fe1_wr_req_ready;
        wr_req_t fe1_wr_req;
        logic   fe1_wr_res_valid, fe1_wr_res_ready;
        wr_res_t fe1_wr_res;

    // --------------------------
    // Backend <=> SCPAD0 / SCPAD1
    // --------------------------
        logic   be0_rd_req_valid, be0_rd_req_ready;
        rd_req_t be0_rd_req;
        logic   be0_rd_res_valid, be0_rd_res_ready;
        rd_res_t be0_rd_res;

        logic   be0_wr_req_valid, be0_wr_req_ready;
        wr_req_t be0_wr_req;
        logic   be0_wr_res_valid, be0_wr_res_ready;
        wr_res_t be0_wr_res;

        logic   be1_rd_req_valid, be1_rd_req_ready;
        rd_req_t be1_rd_req;
        logic   be1_rd_res_valid, be1_rd_res_ready;
        rd_res_t be1_rd_res;

        logic   be1_wr_req_valid, be1_wr_req_ready;
        wr_req_t be1_wr_req;
        logic   be1_wr_res_valid, be1_wr_res_ready;
        wr_res_t be1_wr_res;

    // --------------------------
    // Router <=> SCPAD0 
    // --------------------------
        // ---- Head (Mux from FE or BE)
        logic spad0_wr_sel_valid, spad0_wr_sel_ready;
        sel_wr_req_t spad0_wr_sel_req;
        logic spad0_rd_sel_valid, spad0_rd_sel_ready;
        sel_rd_req_t spad0_rd_sel_req;

        // ---- Write path: W-XBAR0 (swizzle) → SRAM Port-B0 (write)
        logic   w0_in_valid, w0_in_ready;
        xbar_desc_t    w0_in_desc;
        scpad_data_t   w0_in_wdata;

        xbar_sram_w_t  w0_to_sram;    // swizzled beats to SRAM
        sram_w_port_req_t spad0_w_port_req;
        sram_w_port_res_t spad0_w_port_res; // ack with src

        // ---- Read path: SRAM Port-R0 (read) → R-XBAR0 (unswizzle)
        sram_r_port_req_t spad0_r_port_req;
        sram_r_port_res_t spad0_r_port_res;

        // R-XBAR0 outputs unswizzled beats tagged with src for resp-demux
        logic  r0_out_valid, r0_out_ready;
        sel_rd_res_t  r0_out; // {src, rdata}

        // ---- Tail (Resp Arb / Demux to FE or BE)
        logic spad0_wr_resp_valid, spad0_wr_resp_ready;
        sel_wr_res_t spad0_wr_resp; // {src}

        logic spad0_rd_resp_valid, spad0_rd_resp_ready;
        sel_rd_res_t spad0_rd_resp; // {src, rdata}

    // --------------------------
    // Router <=> SCPAD1
    // --------------------------
        // ---- Head (Mux from FE or BE)
        logic spad1_wr_sel_valid, spad1_wr_sel_ready;
        sel_wr_req_t spad1_wr_sel_req;

        logic spad1_rd_sel_valid, spad1_rd_sel_ready;
        sel_rd_req_t spad1_rd_sel_req;

        // ---- Write path: W-XBAR1 → SRAM Port-B1
        logic   w1_in_valid, w1_in_ready;
        xbar_desc_t    w1_in_desc;
        scpad_data_t   w1_in_wdata;

        xbar_sram_w_t  w1_to_sram;
        sram_w_port_req_t spad1_w_port_req;
        sram_w_port_res_t spad1_w_port_res;

        // ---- Read path: SRAM Port-R1 → R-XBAR1
        sram_r_port_req_t spad1_r_port_req;
        sram_r_port_res_t spad1_r_port_res;

        logic  r1_out_valid, r1_out_ready;
        sel_rd_res_t  r1_out;

        // ---- Tail (Resp Arb / Demux)
        logic spad1_wr_resp_valid, spad1_wr_resp_ready;
        sel_wr_res_t spad1_wr_resp;

        logic spad1_rd_resp_valid, spad1_rd_resp_ready;
        sel_rd_res_t spad1_rd_resp;

    // ==========================================================================
    // ============================== MODPORTS =================================
    // ==========================================================================

    // --------------------------
    // Backends
    // --------------------------
        modport sched_backend (
            output sched_req_valid, sched_req,
            input  sched_req_ready, sched_rsp_valid, sched_rsp
        );

        modport backend_sched (
            input  sched_req_valid, sched_req,
            output sched_req_ready, sched_rsp_valid, sched_rsp
        );

        modport backend (
            // → SCPAD0
            output be0_rd_req_valid, be0_rd_req, be0_rd_res_ready,
            input  be0_rd_req_ready, be0_rd_res_valid, be0_rd_res,
            output be0_wr_req_valid, be0_wr_req, be0_wr_res_ready,
            input  be0_wr_req_ready, be0_wr_res_valid, be0_wr_res,
            // → SCPAD1
            output be1_rd_req_valid, be1_rd_req, be1_rd_res_ready,
            input  be1_rd_req_ready, be1_rd_res_valid, be1_rd_res,
            output be1_wr_req_valid, be1_wr_req, be1_wr_res_ready,
            input  be1_wr_req_ready, be1_wr_res_valid, be1_wr_res
        );


        modport backend_dram_ports (
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

    // --------------------------
    // Frontends 
    // --------------------------
        modport frontend0 (
            // READ
            output fe0_rd_req_valid, fe0_rd_req, fe0_rd_res_ready,
            input  fe0_rd_req_ready, fe0_rd_res_valid, fe0_rd_res,
            // WRITE
            output fe0_wr_req_valid, fe0_wr_req, fe0_wr_res_ready,
            input  fe0_wr_req_ready, fe0_wr_res_valid, fe0_wr_res
        );

        modport frontend1 (
            // READ
            output fe1_rd_req_valid, fe1_rd_req, fe1_rd_res_ready,
            input  fe1_rd_req_ready, fe1_rd_res_valid, fe1_rd_res,
            // WRITE
            output fe1_wr_req_valid, fe1_wr_req, fe1_wr_res_ready,
            input  fe1_wr_req_ready, fe1_wr_res_valid, fe1_wr_res
        );


    // --------------------------
    // Per-SCPAD Head (Req MUX with BE>FE priority)
    // --------------------------
        modport spad0_head (
            // Inputs from FE0 & BE0
            input  fe0_rd_req_valid, fe0_rd_req, fe0_rd_res_ready,
                fe0_wr_req_valid, fe0_wr_req, fe0_wr_res_ready,
                be0_rd_req_valid, be0_rd_req, be0_rd_res_ready,
                be0_wr_req_valid, be0_wr_req, be0_wr_res_ready,
            output fe0_rd_req_ready, fe0_wr_req_ready, be0_rd_req_ready, be0_wr_req_ready,

            // Selected outputs toward path
            output spad0_wr_sel_valid, spad0_wr_sel_req,
                spad0_rd_sel_valid, spad0_rd_sel_req,
            input  spad0_wr_sel_ready, spad0_rd_sel_ready
        );

        modport spad1_head (
            input  fe1_rd_req_valid, fe1_rd_req, fe1_rd_res_ready,
                fe1_wr_req_valid, fe1_wr_req, fe1_wr_res_ready,
                be1_rd_req_valid, be1_rd_req, be1_rd_res_ready,
                be1_wr_req_valid, be1_wr_req, be1_wr_res_ready,
            output fe1_rd_req_ready, fe1_wr_req_ready, be1_rd_req_ready, be1_wr_req_ready,

            output spad1_wr_sel_valid, spad1_wr_sel_req,
                spad1_rd_sel_valid, spad1_rd_sel_req,
            input  spad1_wr_sel_ready, spad1_rd_sel_ready
        );

    // --------------------------
    // Per-SCPAD Tail (Resp Arb/Demux back to FE/BE)
    // --------------------------
        modport spad0_tail (
            // in from SRAM write ack and R-XBAR0
            input  spad0_wr_resp_valid, spad0_wr_resp,
                spad0_rd_resp_valid, spad0_rd_resp,
            output spad0_wr_resp_ready, spad0_rd_resp_ready,

            // out to FE0 & BE0
            output fe0_wr_res_valid, fe0_wr_res,
                fe0_rd_res_valid, fe0_rd_res,
                be0_wr_res_valid, be0_wr_res,
                be0_rd_res_valid, be0_rd_res,
            input  fe0_wr_res_ready, fe0_rd_res_ready,
                be0_wr_res_ready, be0_rd_res_ready
        );

        modport spad1_tail (
            input  spad1_wr_resp_valid, spad1_wr_resp,
                spad1_rd_resp_valid, spad1_rd_resp,
            output spad1_wr_resp_ready, spad1_rd_resp_ready,

            output fe1_wr_res_valid, fe1_wr_res,
                fe1_rd_res_valid, fe1_rd_res,
                be1_wr_res_valid, be1_wr_res,
                be1_rd_res_valid, be1_rd_res,
            input  fe1_wr_res_ready, fe1_rd_res_ready,
                be1_wr_res_ready, be1_rd_res_ready
        );
        
    // --------------------------
    // Write-XBARs (2 total)
    // --------------------------
        modport xbar_w0 (
            input  w0_in_valid, w0_in_desc, w0_in_wdata,
            output w0_in_ready,
            output w0_to_sram
        );

        modport xbar_w1 (
            input  w1_in_valid, w1_in_desc, w1_in_wdata,
            output w1_in_ready,
            output w1_to_sram
        );

    // --------------------------
    // Read-XBARs (2 total)
    // --------------------------
        modport xbar_r0 (
            input  spad0_r_port_res,
            output r0_out_valid, r0_out,
            input  r0_out_ready
        );

        modport xbar_r1 (
            input  spad1_r_port_res,
            output r1_out_valid, r1_out,
            input  r1_out_ready
        );

    // --------------------------
    // SRAM Controller (both SCPADs; contains both SRAM-Arb stages)
    // --------------------------
        modport sram_ctrl (
            // SCPAD0 write port (after W-XBAR0)
            input  spad0_w_port_req,
            output spad0_w_port_res,
            // SCPAD0 read port (before R-XBAR0)
            input  spad0_r_port_req,
            output spad0_r_port_res,

            // SCPAD1 write port (after W-XBAR1)
            input  spad1_w_port_req,
            output spad1_w_port_res,
            // SCPAD1 read port (before R-XBAR1)
            input  spad1_r_port_req,
            output spad1_r_port_res
        );

    // --------------------------
    // Glue between Head <-> XBARs <-> SRAM ctrl <-> XBARS <-> Tail (per SCPAD)
    // --------------------------
        modport spad0_path (
            // Head-selected requests
            input  spad0_wr_sel_valid, spad0_wr_sel_req,
                spad0_rd_sel_valid, spad0_rd_sel_req,
            output spad0_wr_sel_ready, spad0_rd_sel_ready,

            // W-XBAR0
            output w0_in_valid, w0_in_desc, w0_in_wdata,
            input  w0_in_ready, w0_to_sram,

            // To/From SRAM ctrl
            output spad0_w_port_req, spad0_r_port_req,
            input  spad0_w_port_res, spad0_r_port_res,

            // From R-XBAR0
            input  r0_out_valid, r0_out,
            output r0_out_ready,

            // To Tail
            output spad0_wr_resp_valid, spad0_wr_resp,
                spad0_rd_resp_valid, spad0_rd_resp,
            input  spad0_wr_resp_ready, spad0_rd_resp_ready
        );

        modport spad1_path (
            input  spad1_wr_sel_valid, spad1_wr_sel_req,
                spad1_rd_sel_valid, spad1_rd_sel_req,
            output spad1_wr_sel_ready, spad1_rd_sel_ready,

            output w1_in_valid, w1_in_desc, w1_in_wdata,
            input  w1_in_ready, w1_to_sram,

            output spad1_w_port_req, spad1_r_port_req,
            input  spad1_w_port_res, spad1_r_port_res,

            input  r1_out_valid, r1_out,
            output r1_out_ready,

            output spad1_wr_resp_valid, spad1_wr_resp,
                spad1_rd_resp_valid, spad1_rd_resp,
            input  spad1_wr_resp_ready, spad1_rd_resp_ready
        );

endinterface
`endif
