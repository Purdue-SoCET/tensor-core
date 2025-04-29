`ifndef ISSUE_IF_VH
`define ISSUE_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface issue_if;
    import isa_pkg::*;
    import datapath_pkg::*;

    //Inputs from dispatch
    dispatch_t dispatch;
    fu_type n_fu_t;
    fust_s_row_t n_fust_s;
    fust_m_row_t n_fust_m;
    fust_g_row_t n_fust_g;
    fu_scalar_t n_fu_s;
    // logic n_fu_m, n_fu_g;
    logic n_fust_s_en, n_fust_m_en, n_fust_g_en;
    logic [2:0][1:0] n_t1;
    logic [2:0][1:0] n_t2;

    logic [1:0] n_gt1;
    logic [1:0] n_gt2;
    logic [1:0] n_gt3;

    logic [1:0] n_mt1;

    // Inputs to latch
    // logic flush;

    // Inputs from execute
    // ex_t ex; //branch and matrix done signals
    logic branch_miss;
    logic branch_resolved;
    logic [4:0] fu_ex;
    logic freeze;
    // Inputs from writeback
    wb_t wb; //alu and ld/st done signals
    word_t s_wdata;
    
    // Outputs of stage
    issue_t out;
    fust_s_t fust_s;
    fust_m_t fust_m;
    fust_g_t fust_g;
    fust_state_e [4:0] fust_state;
    
    modport IS (
        input dispatch, wb, n_fu_t, n_fust_s, n_fust_m, n_fust_g, n_fu_s, n_fust_s_en, n_fust_m_en, n_fust_g_en, 
        input n_t1, n_t2, s_wdata, branch_miss, branch_resolved, fu_ex, n_mt1, n_gt1, n_gt2, n_gt3, freeze,
        output out, fust_s, fust_m, fust_g, fust_state
    );

endinterface
`endif
