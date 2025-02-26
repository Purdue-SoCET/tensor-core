`include "isa_types.vh"
`include "datapath_types.vh"
`include "fu_branch_predictor_if.vh"
`include "fetch_if.vh"
`include "fetch_branch_if.vh"
`include "fu_branch_if.vh"

module fetch_branch (
    input CLK, 
    input nRST, 
    fetch_branch_if.fb fbif
);
import isa_pkg::*;

//grab ihit from a different interface, from i cache possibly
logic ihit = 1;

fu_branch_if fubif();
fu_branch_predictor_if fubpif();
fetch_if fif();

fu_branch BRANCH (CLK, nRST, fubif);
fu_branch_predictor PRED (CLK, nRST, fubpif);
fetch FETCH (CLK, nRST, ihit, fif);

//Fetch_branch connections

assign fubif.branch = fbif.branch; //fetch_branch
assign fubif.branch_type = fbif.branch_type;
assign fubif.branch_gate_sel = fbif.branch_gate_sel;
assign fubif.reg_a = fbif.reg_a;
assign fubif.reg_b = fbif.reg_b;
assign fubif.current_pc = fbif.current_pc;
assign fubif.imm = fbif.imm;
assign fubif.predicted_outcome = fbif.predicted_outcome;

//Branch to branch predictor connections
assign fubpif.pc = fbif.current_pc; //current pc for branch predictor
assign fubpif.update_btb = fubif.update_btb;
assign fubpif.branch_outcome = fubif.branch_outcome;
assign fubpif.update_pc = fubif.updated_pc;
assign fubpif.branch_target = fubif.branch_target;

//Branch predictor to fetch connections
assign fif.misprediction = fubif.misprediction;
assign fif.pc_prediction = fubpif.predicted_target;
assign fif.correct_target = fubif.updated_pc; //correct prediction
assign fif.correct_pc = fubif.correct_pc;

//Fetch_branch to fetch connections
assign fif.imemload = fbif.imemload;
assign fif.flush = fbif.flush;
assign fif.stall = fbif.stall;
assign fif.dispatch_free = fbif.dispatch_free;
assign fif.ihit = fbif.ihit;

assign fbif.pc = fif.pc;
assign fbif.instr = fif.instr;

endmodule 