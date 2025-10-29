`include "isa_types.vh"
`include "datapath_types.vh"
`include "fetch_tbp_if.vh"
`include "btb_if.vh"
`include "bpt_if.vh"
`include "bpt_tbp_if.vh"


module fetch_tbp#( 	
    parameter size = 11)
(
    input logic CLK, 
    input logic nRST, 
    fetch_tbp_if.tbp tbpif
);

    //--------------Global BTB--------------------
    btb_if btbif();

    //resolution stage

    assign btbif.pc_res = tbpif.pc_res;
    assign btbif.bt_res = tbpif.bt_res;
    assign btbif.enable_res = tbpif.enable_res;

    //fetch stage
    assign btbif.pc_fetch = tbpif.pc_fetch;

    btb #(.size(size)) BTB(.CLK(CLK), .nRST(nRST), .btbif(btbif));
 
    //--------------G-Share Predictor (Predictor 1)--------------
    //GHR
    logic [2:0] GHR_out;
    nbit_stp_shiftreg #(.size(3)) GHR(.CLK(CLK), .nRST(nRST), .enable(tbpif.enable_res), .in(tbpif.taken_res), .out(GHR_out));

    //BPT
    bpt_if bpt_gshareif();

    //resolution stage
    assign bpt_gshareif.pc_res = tbpif.pc_res;
    assign bpt_gshareif.taken_res = tbpif.taken_res;
    assign bpt_gshareif.enable_res = tbpif.enable_res;

    //fetch stage
    assign bpt_gshareif.pc_fetch = {tbpif.pc_fetch[31:5],tbpif.pc_fetch[4:2] ^ GHR_out, tbpif.pc_fetch[1:0]}; //indexed with PC XOR GHR

    bpt #(.size(size)) bpt_gshare(.CLK(CLK), .nRST(nRST), .bptif(bpt_gshareif));

    //--------------2bit Predictor (Predictor 0)--------------
    //BPT
    bpt_if bpt_2bitif();

    //resolution stage
    assign bpt_2bitif.pc_res = tbpif.pc_res;
    assign bpt_2bitif.taken_res = tbpif.taken_res;
    assign bpt_2bitif.enable_res = tbpif.enable_res;

    //fetch stage
    assign bpt_2bitif.pc_fetch = tbpif.pc_fetch;

    bpt #(.size(size)) bpt_2bit(.CLK(CLK), .nRST(nRST), .bptif(bpt_2bitif));

    //--------------Tournament Predictor--------------
    //BPT
    bpt_tbp_if bpt_tbpif();

    //resolution stage
    assign bpt_tbpif.pc_res = tbpif.pc_res;
    assign bpt_tbpif.taken_res = {bpt_gshareif.pred_correct, bpt_2bitif.pred_correct};
    assign bpt_tbpif.enable_res = tbpif.enable_res;

    //fetch stage
    assign bpt_tbpif.pc_fetch = tbpif.pc_fetch;

    bpt_tbp #(.size(size)) bpt_tbp(.CLK(CLK), .nRST(nRST), .bpt_tbpif(bpt_tbpif));

    //------------Top Level Outputs
    logic taken;
    //choose bewteen pred1 (ghsare) or pred2 (2bit) depending on prediction from tbp
    assign taken = (bpt_tbpif.pred_fetch) ? bpt_gshareif.pred_fetch : bpt_2bitif.pred_fetch;

    always_comb begin : nxt_PC
        if(tbpif.enable_fetch && taken) begin //if b-type AND taken
            tbpif.nxt_PC = btbif.bt_fetch;
        end
        else begin //if not b-type
            tbpif.nxt_PC = tbpif.pc_fetch + 4;
        end
    end
endmodule