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
      // fetch data coming from fetch stage to dispatch 
      diif.fetch = sbif.fetch;

      // fusts coming from issue to dispatch
      // diif.fust_s = isif.fust_s;
      diif.fust_s_out_busy = isif.fust_s_out_busy;
      diif.fust_s_out_t1 = isif.fust_s_out_t1;  
      diif.fust_s_out_t2 = isif.fust_s_out_t2;  
      diif.fust_s_out_op_alu = isif.fust_s_out_op_alu;
      diif.fust_s_out_op_sls = isif.fust_s_out_op_sls;
      diif.fust_s_out_op_br = isif.fust_s_out_op_br;

      diif.fust_m = isif.fust_m;
      diif.fust_g = isif.fust_g;
      diif.fust_state = isif.fust_state;

      // necessary wb data coming from writeback stage and scratchpad
      diif.wb = sbif.wb_dispatch;
      isif.wb = sbif.wb_issue;

      // output of dispatch going into issue
      isif.dispatch = diif.out;

      // combinational next data (fust, tags, enables) going from dispatch to issue 
      isif.n_fust_s = diif.n_fust_s;
      isif.n_fust_m = diif.n_fust_m;
      isif.n_fust_g = diif.n_fust_g;
      isif.n_fu_t = diif.n_fu_t;
      isif.n_fu_s = diif.n_fu_s;
      isif.n_t1   = diif.n_t1;
      isif.n_t2   = diif.n_t2;
      isif.n_s_t1 = diif.n_s_t1;
      isif.n_m_t2 = diif.n_m_t2;
      isif.n_gt1 = diif.n_gt1;
      isif.n_gt2 = diif.n_gt2;
      isif.n_gt3 = diif.n_gt3;
      isif.n_fust_s_en = diif.n_fust_s_en;
      isif.n_fust_m_en = diif.n_fust_m_en;
      isif.n_fust_g_en = diif.n_fust_g_en;

      // fu_ex tells issue and dispatch when a funtional unit has finished
      isif.fu_ex = sbif.fu_ex;
      diif.fu_ex = sbif.fu_ex;

      // branch/jump related signals
      isif.branch_miss = sbif.branch_miss;
      diif.branch_miss = sbif.branch_miss;
      diif.branch_resolved = sbif.branch_resolved;
      isif.branch_resolved = sbif.branch_resolved;
      sbif.jump = diif.jump;

      // freeze is set when dispatch sees a hazard
      sbif.freeze = diif.freeze;
      isif.freeze = diif.freeze;
      
      // halt output signals 
      sbif.halt = isif.halt;
      sbif.fetch_halt = diif.halt;
      
      // output of scoreboard is the output from issue going into execute stage
      sbif.out = isif.out;
    end
endmodule
