`include "isa_types.vh"
`include "datapath_types.vh"
`include "fu_branchpred_if.vh"
`include "fetch_if.vh"
`include "fetch_branch_if.vh"

module fetch_branch (input CLK, input nRST, fetch_branch_if.fb fbif);

fu_branchpred_if fubrif();
fetch_if fif();
fu_branch_if fubif();

fu_branchpred(CLK, nRST, fubrif);
fetch(CLK, nRST, fif);
fu_branch(CLK, nRST, fubrif);

//actual outcome of the branch goes into the branch predictor to tell the fetch unit if the prediction was correct or not
//connections to branch predictor from the branch functional unit
assign fubrif.pc = fubif.pc;
assign furbrif.updated_pc = fubif.updated_pc;
assign fubrif.branch_outcome = fubif.branch_outcome;
assign fubrif.branch_target = fubif.branc_target;

assign fif.pc = furbif.updated_pc;
assign fif.predicted_outcome = fubrif.predicted_outcome;
assign fbif.fetch_load = fif.fetch_load; //sets the fetch load to the fetch unit load


endmodule 