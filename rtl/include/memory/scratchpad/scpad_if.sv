/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`ifndef SCPAD_IF_SV
`define SCPAD_IF_SV

interface scpad_if (input logic clk, input logic n_rst);
    `include "scpad_params.svh"

    import scpad_pkg::*;

    // ----------------------------------------------------------------------
    // Wires
    // ----------------------------------------------------------------------

    // Backend <=> DRAM Cntrl.
    logic be_dram_stall [NUM_SCPADS];
    dram_req_t be_dram_req [NUM_SCPADS];
    dram_res_t dram_be_res [NUM_SCPADS];

    // Scheduler <=> Backend 
    sched_req_t sched_req [NUM_SCPADS];
    sched_res_t sched_res [NUM_SCPADS];

    // Backend <=> Body  
    logic be_stall [NUM_SCPADS]; 
    req_t  be_req  [NUM_SCPADS];
    res_t  be_res  [NUM_SCPADS];

    // Vector <=> Frontend 
    logic fe_vec_stall [NUM_SCPADS];
    req_t  vec_req  [NUM_SCPADS];
    res_t vec_res  [NUM_SCPADS];

    // Frontend <=> Body 
    logic fe_stall [NUM_SCPADS];
    req_t  fe_req [NUM_SCPADS];
    res_t  fe_res  [NUM_SCPADS];

    // Head <=> Stomach <=> Tail 
    logic w_stall [NUM_SCPADS]; 
    logic r_stall [NUM_SCPADS]; 

    // Head => Stomach => Tail (Write)
    sel_req_t head_stomach_req [NUM_SCPADS]; // into wr xbar
    sel_req_t xbar_cntrl_req [NUM_SCPADS]; // into body fifo 
    sel_req_t cntrl_spad_req [NUM_SCPADS]; // into spad 
    sel_res_t spad_xbar_req [NUM_SCPADS]; // into rd xbar
    sel_res_t stomach_tail_res [NUM_SCPADS]; // into tail 

    // Spad Done.
    mask_t spad_busy [NUM_SCPADS]; 
    mask_t spad_cntrl_res [NUM_SCPADS]; 

    // ----------------------------------------------------------------------
    // External Modport definitions
    // ----------------------------------------------------------------------

    modport dram_backend (
        input be_dram_stall, be_dram_req,
        output dram_be_res
    );

    modport vec_frontend (
        input  fe_vec_stall, vec_res, 
        output vec_req
    );

    modport sched_backend (
        output sched_req,
        input sched_res
    );

    // ----------------------------------------------------------------------
    // Internal Modport definitions
    // ----------------------------------------------------------------------

    // Scheduler <=> Backend
    modport backend_sched (
        input clk, n_rst, sched_req,
        output sched_res
    );

    // Backend <=> Body
    modport backend_body (
        input clk, n_rst, 
        input  be_stall, be_res, 
        output be_req
    );

    // Backend <=> DRAM
    modport backend_dram (
        input clk, n_rst, 
        output be_dram_req, be_dram_stall,
        input dram_be_res
    );

    // Vec. Core <=> Frontend 
    modport frontend_vec (
        input clk, n_rst, 
        input  vec_req,
        output fe_vec_stall, vec_res
    );

    // Frontend <=> Body
    modport frontend_body (
        input clk, n_rst, 
        input fe_stall, fe_res,
        output fe_req
    );

    // Write crossbar
    modport xbar_w (
        input clk, n_rst, 
        input w_stall,
        input head_stomach_req,
        output xbar_cntrl_req
    );

    // Read crossbar
    modport xbar_r (
        input clk, n_rst, 
        input r_stall,
        input spad_xbar_req,
        output stomach_tail_res
    );

    // SRAM Controller
    modport sram_ctrl (
        input clk, n_rst, 
        output w_stall, r_stall,
        input spad_busy, 
        input  head_stomach_req,
        input  spad_cntrl_res,
        input  xbar_cntrl_req,
        output cntrl_spad_req,
        output spad_xbar_req,
        output stomach_tail_res
    );

    // Head (Req MUX with BE > FE priority) per scratchpad
    modport spad_head (
        input clk, n_rst, 
        // Downstream backpressure
        input w_stall, r_stall,
        // Header backpresssure. 
        output fe_stall, be_stall,
        // Inputs from FE and BE
        input fe_req, be_req,
        // Outputs toward Body
        output head_stomach_req

    );


    // Tail (Resp Arb/Demux back to FE/BE) per scratchpad
    // Won't stall. 
    modport spad_tail (
        input clk, n_rst, 
        input  stomach_tail_res,
        output fe_res, be_res
    );

    // Body: Head <=> XBARs <=> SRAM ctrl <=> XBARs <=> Tail 
    modport spad_body (
        input clk, n_rst, 
        // Inputs from FE/BE
        input fe_req, be_req,
        // Outputs back to FE/BE
        output fe_stall, be_stall, fe_res, be_res
    );

    // ----------------------------------------------------------------------
    // Top-level modport 
    // ----------------------------------------------------------------------
    modport top (
        input clk, n_rst, 
        // Scheduler <=> Backend
        output sched_req,
        input sched_res,

        // Backend <=> DRAM
        output be_dram_req,
        input be_dram_stall,
        input dram_be_res,

        // Vector Core <=> Frontend
        input vec_req,
        input fe_vec_stall,
        output vec_res
    );

    // ----------------------------------------------------------------------
    // Performance Counters
    // ----------------------------------------------------------------------

    `ifndef SYNTHESIS
        logic [63:0] scpad_backpressure_buffer_read_empty [NUM_SCPADS];  
        logic [63:0] scpad_backpressure_buffer_read_stall [NUM_SCPADS];  
        logic [63:0] scpad_backpressure_buffer_write_empty [NUM_SCPADS]; 
        logic [63:0] scpad_backpressure_buffer_write_stall [NUM_SCPADS];  
    `endif

    // ----------------------------------------------------------------------
    // Testbench Definitions
    // ----------------------------------------------------------------------

    // Backend TB
    modport backend_tb (
        input clk, n_rst, 
        input sched_res, be_req,
        input be_dram_stall, be_dram_req,

        output be_stall,
        output sched_req, be_res, dram_be_res
    );

    // Frontend TB
    modport frontend_tb (
        input clk, n_rst, 
        input fe_vec_stall, vec_res, fe_req,

        output fe_stall, fe_res, vec_req
    );

    // Write Crossbar TB
    modport xbar_w_tb (
        input clk, n_rst, 
        input xbar_cntrl_req,

        output w_stall, head_stomach_req
    );

    // Read Crossbar TB
    modport xbar_r_tb (
        input clk, n_rst, 
        input stomach_tail_res,

        output r_stall, spad_xbar_req
    );

    // SRAM Controller TB
    modport sram_ctrl_tb (
        input clk, n_rst, 
        input w_stall, r_stall,
        input cntrl_spad_req, spad_xbar_req, 
        input stomach_tail_res,

        output spad_busy, head_stomach_req,
        output spad_cntrl_res, xbar_cntrl_req
    );

    // Head TB
    modport spad_head_tb (
        input clk, n_rst, 
        input fe_stall, be_stall,
        input head_stomach_req,

        output w_stall, r_stall,
        output fe_req, be_req
    );

    // Tail TB
    modport spad_tail_tb (
        input clk, n_rst, 
        input fe_res, be_res,
        output  stomach_tail_res
    );

    // Body TB
    modport spad_body_tb (
        input clk, n_rst, 
        input fe_stall, be_stall, fe_res, be_res,
        output fe_req, be_req
    );

endinterface

`endif 
