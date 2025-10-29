`include "datapath_types.vh"
`include "scoreboard_if.vh"
`include "dispatch.sv"
`include "dispatch_if.vh"
`include "issue.sv"
`include "issue_if.vh"

module scoreboard(
    input logic CLK, nRST,
    scoreboard_if.SB sbif
);

    import isa_pkg::*;
    import datapath_pkg::*;

    dispatch_if diif();
    issue_if isif();

    dispatch DI (CLK, nRST, diif);
    issue IS (CLK, nRST, isif);


    always_comb begin
      diif.fetch = sbif.fetch;
      // diif.flush = sbif.flush;

      diif.fust_s = isif.fust_s;
      diif.fust_m = isif.fust_m;
      diif.fust_g = isif.fust_g;
      diif.fust_state = isif.fust_state;
      diif.wb = sbif.wb_ctrl;

      isif.dispatch = diif.out;
      // isif.flush = sbif.flush;
      isif.wb = sbif.wb;

      isif.n_fust_s = diif.n_fust_s;
      isif.n_fust_m = diif.n_fust_m;
      isif.n_fust_g = diif.n_fust_g;

      isif.n_fu_t = diif.n_fu_t;
      isif.n_fu_s = diif.n_fu_s;
      isif.n_t1   = diif.n_t1;
      isif.n_t2   = diif.n_t2;
      // isif.n_fu_m = diif.n_fu_m;
      // isif.n_fu_g = diif.n_fu_g;

      isif.n_fust_s_en = diif.n_fust_s_en;
      isif.n_fust_m_en = diif.n_fust_m_en;
      isif.n_fust_g_en = diif.n_fust_g_en;

      isif.s_wdata = sbif.s_wdata;

      isif.fu_ex = sbif.fu_ex;
      diif.fu_ex = sbif.fu_ex;

      isif.branch_miss = sbif.branch_miss;
      diif.branch_miss = sbif.branch_miss;
      diif.branch_resolved = sbif.branch_resolved;

      sbif.out = isif.out;
    end
endmodule
