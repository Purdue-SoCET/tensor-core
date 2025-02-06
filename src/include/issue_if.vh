`ifndef ISSUE_IF_VH
`define ISSUE_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface issue_if;
    import isa_pkg::*;
    import datapath_pkg::*;

    //Inputs from dispatch
    dispatch_t dispatch;
    fust_s_row_t n_fust_s;
    fust_m_row_t n_fust_m;
    fust_g_row_t n_fust_g;
    fu_scalar_t n_fu_s;
    logic n_fu_m, n_fu_g;
    logic n_fust_s_en, n_fust_m_en, n_fust_g_en;

    // Inputs to latch
    logic flush, freeze;

    // Inputs from writeback
    wb_ctr_t wb;
    regbits_t s_wdata;
    
    // Outputs of stage
    issue_t out;
    fust_s_t fust_s;
    fust_m_t fust_m;
    fust_g_t fust_g;
    
    modport IS (
        input dispatch, flush, freeze, wb, n_fust_s, n_fust_m, n_fust_g, n_fu_s, n_fu_m, n_fu_g, n_fust_s_en, n_fust_m_en, n_fust_g_en, s_wdata,
        output out, fust_s, fust_m, fust_g
    );

endinterface
`endif
