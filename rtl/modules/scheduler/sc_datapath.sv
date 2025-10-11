// PIPELINE PACKAGES
`include "pipeline_types.vh"

// INTERFACES
`include "fetch_if.vh"
`include "scoreboard_if.vh"
`include "dispatch_if.vh"
`include "issue_if.vh"
`include "regfile_if.vh"
`include "execute_if.vh"
`include "writeback_if.vh"
`include "datapath_cache_if.vh"

module sc_datapath
(
    input logic CLK, nrst,
    datapath_cache_if.dp dcif
);
    fetch_if fif();
    fetch FETCH (CLK, nrst, dcif.ihit, fif);

    scoreboard_if sbif();
    scoreboard SCOREBOARD (CLK, nrst, sbif);

    dispatch_if dif();
    dispatch DISPATCH (CLK, nrst, dif);
    
    issue_if isif();
    issue ISSUE (CLK, nrst, isif);
    
    regfile_if rfif();
    // regfile REGFILE (CLK, nrst, fuif);
    regfile REGFILE (CLK, nrst, rfif);

    execute_if eif();
    execute EXECUTE (CLK, nrst, eif);

    writeback_if wbif();
    writeback WRITEBACK (CLK, nrst, wbif);

// IMPORT PACKAGE
    import pipeline_pkg::*;
    import isa_pkg::*;
    import datapath_pkg::*;

// LATCH INSTANTIATIONS

    fd_t fd_fetch;
    fd_t fd_dispatch;

    ie_t ie_issue;
    ie_t ie_execute;

    ew_t ew_execute;
    ew_t ew_writeback;

//  FETCH/DISPATCH CONNECTIONS
    
    //FETCH CONNECTIONS
    assign fif.imemload = dcif.imemload;
    //assign fif.flush = 
    //assign fif.stall = eif.
    //assign fif.dispatch_free =
    // assign fif.pc_prediction = eif.pc_fetch;
    // assign fif.misprediction = eif.pred_outcome;
    // assign fif.correct_target = eif.branch_target;
    
    //BEFORE LATCH
    assign fd_fetch.instr = fif.instr;
    assign fd_fetch.pc = fif.pc;

    //AFTER LATCH CONNECTIONS
    assign sbif.fetch = fd_dispatch.instr;

//  ISSUE/EXECUTE CONNECTIONS

    //BEFORE LATCH
    assign ie_issue.rdat1 = rfif.rdat1;
    assign ie_issue.rdat2 = rfif.rdat2;
    assign ie_issue.out = sbif.out;
    assign ie_issue.fust_s = isif.fust_s;
    assign ie_issue.fust_m = isif.fust_m;
    assign ie_issue.fust_g = isif.fust_g;
    assign ie_issue.pc = fd_dispatch.pc;
    
    //BRANCH FU
    // assign eif.ihit = dcif.ihit; 
    // // assign eif.bfu_branch_outcome = fubpif.predicted_outcome;
    // // assign bfu_update_btb =
    // //this is an output in the functional unit???
    // // assign eif.bfu_branch_target = fubpif.predicted_targe;
    // assign eif.bfu_pc = ie_issue.pc;
    // assign eif.bfu_pc_fetch = fif.pc;

    // //SCALAR ALU
    // assign eif.salu_aluop = cuif.alu_op;
    // assign eif.salu_port_a = ie_execute.rdat1;
    // assign eif.salu_port_b = ie_execute.rdat2;
    // assign eif.imm = cuif.imm;

    // //SCALAR LOAD/STORE
    // assign eif.sls_mem_type = cuif.s_mem_type;
    // assign eif.sls_rs1 = rfif.rdat1; //didnt know where to find rsel signal control unit does not decode it
    // assign eif.sls_rs2 = rfif.rdat2;
    // assign eif.sls_dmem_in = cuif.s_reg_write;
    // assign eif.sls_dhit_in = dcif.dhit;

    //AFTER LATCH CONNECTIONS
    // assign fuslsif.rs1 = rfif.rdat1;
    // assign fuslsif.rs2 = rfif.rdat2;
    // assign fuslsif.imm =
    // assign fuslsif.mem_type =
    // assign fuslsif. dmem_in = 
    // assign fuslsif.dhit_in =
    // assign fubif.pc = ie_execute.pc;
    // assign fualuif.port_a = ie_execute.rdat1;
    // assign fualuif.port_b = ie_execute.rdat2;
    // assign fualif.aluop =

    // //BRANCH FU TO FETCH CONNECTIONS
    // assign fubif.pc_fetch = fif.pc; //maybe need this idk

    // //FETCH TO BRANCH FU CONNECTIONS
    // assign fif.pc_prediction = fubif.pred_outcome;
    // assign fif.correct_target = fubif.pred_target;
    
    //WRITEBACK TO SCALAR ALU FU CONNECTIONS
    // assign wbif.wb_select = eif.dmemaddr;
    // assign wbif.store_out = eif.dmemstore;
    
    // //WRITEBACK TO SCALAR LOAD/STORE FU CONNECTIONS
    // assign wbif.alu_out = eif.port_output;

//  EXECUTE/WRITEBACK CONNECTIONS
    
    //BEFORE LATCH
    assign ew_execute.wb_data = wbif.wb_out;

    //AFTER LATCH
    assign sbif.wb = ew_writeback;

// FLIP-FLOP FOR LATCHES

    always_ff @(posedge CLK, negedge nrst) begin
        if (nrst == 0) begin
            fd_dispatch <= 0;
            ie_execute <= 0;
            ew_writeback <= 0;
        end
        else begin
            fd_dispatch <= fd_fetch;
            ie_execute <= ie_issue;
            ew_writeback <= ew_execute;
        end
    end

endmodule
