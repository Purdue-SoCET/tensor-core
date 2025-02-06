`ifndef DISPATCH_IF_VH
`define DISPATCH_IF_VH
`include "datapath_types.vh"

interface dispatch_if;
    import datapath_pkg::*;

    //Inputs from fetch
    // typedef logic [2:0] fetch_t;
    fetch_t fetch;

    // Inputs to latch
    logic flush, freeze;

    // Inputs from issue 
    fust_s_t fust_s;
    fust_m_t fust_m;
    fust_g_t fust_g;

    // Inputs from writeback
    wb_ctr_t wb;
    
    // Inputs from memory
    logic ihit;
    
    // Outputs of stage
    dispatch_t out;
    fust_s_row_t n_fust_s;
    fust_m_row_t n_fust_m;
    fust_g_row_t n_fust_g;
    fu_scalar_t n_fu_s;
    logic n_fust_s_en, n_fust_m_en, n_fust_g_en;
    
    modport DI (
        input fetch, flush, freeze, fust_s, fust_m, fust_g, wb, ihit,
        output out, n_fust_s, n_fust_m, n_fust_g, n_fu_s, n_fust_s_en, n_fust_m_en, n_fust_g_en
    );

    modport tb (
        input out, n_fust_s, n_fust_m, n_fust_g, n_fu_s, n_fust_s_en, n_fust_m_en, n_fust_g_en,
        output fetch, flush, freeze, fust_s, fust_m, fust_g, wb, ihit
    );

endinterface
`endif
