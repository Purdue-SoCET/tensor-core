`ifndef DISPATCH_IF_VH
`define DISPATCH_IF_VH
`include "datapath_types.vh"

interface dispatch_if;
    import datapath_pkg::*;

    //Inputs from fetch
    // typedef logic [2:0] fetch_t;
    fetch_t fetch;

    // Inputs to latch
    // logic flush;

    // Inputs from issue 
    fust_s_t fust_s;
    fust_m_t fust_m;
    fust_g_t fust_g;
    fust_state_e [4:0] fust_state;

    // Inputs from writeback
    wb_ctr_t wb;
    
    // Inputs from memory
    logic ihit;

    // Input from execute
    logic branch_resolved;
    logic branch_miss;
    fu_done_signals fu_ex;
    
    // Outputs of stage
    dispatch_t out;
    fust_s_row_t n_fust_s;
    fust_m_row_t n_fust_m;
    fust_g_row_t n_fust_g;
    fu_scalar_t n_fu_s;
    fu_type n_fu_t;
    logic n_fust_s_en, n_fust_m_en, n_fust_g_en;
    logic [2:0][1:0] n_t1;
    logic [2:0][1:0] n_t2;
    
    modport DI (
        input fetch, fust_s, fust_m, fust_g, fust_state, wb, ihit, branch_resolved, branch_miss, fu_ex,
        output out, n_fu_t, n_fust_s, n_fust_m, n_fust_g, n_fu_s, n_fust_s_en, n_fust_m_en, n_fust_g_en, n_t1, n_t2
    );

    modport tb (
        input out, n_fu_t, n_fust_s, n_fust_m, n_fust_g, n_fu_s, n_fust_s_en, n_fust_m_en, n_fust_g_en, n_t1, n_t2,
        output fetch, fust_s, fust_m, fust_g, fust_state, wb, ihit, branch_resolved, branch_miss, fu_ex
    );

endinterface
`endif