`include "isa_types.vh"
`include "datapath_types.vh"
`include "bpt_tbp_if.vh"

module bpt_tbp #( 	
    parameter size = 11)
(
    input logic CLK, 
    input logic nRST, 
    bpt_tbp_if.bpt_tbp bpt_tbpif
);
    //Internal Signals
    localparam strongly_Pred1   = 2'b11; //upper bit 1 = taken
    localparam weakly_Pred1     = 2'b10;
    localparam strongly_Pred0   = 2'b00; //upper bit 0 = not taken
    localparam weakly_Pred0     = 2'b01;

    logic [((2**size)-1):0] [1:0] bpt_tbp;

    logic [1:0] curr_bpt_tbp, nxt_bpt_tbp;

    //--------------Fetch Stage------------------
    //index into bpt_tbp for branch target, using fetch PC (Upper bit gives prediction)
    assign bpt_tbpif.pred_fetch = bpt_tbp[bpt_tbpif.pc_fetch[((size-1)+2):2]][1];

    //-------------Resolution Stage--------------
    //index into bpt_tbp from resolution state to find current state
    assign curr_bpt_tbp = bpt_tbp[bpt_tbpif.pc_res[((size-1)+2):2]];

    always_comb begin
        nxt_bpt_tbp = curr_bpt_tbp;
        casez(curr_bpt_tbp)
            strongly_Pred1  : begin
                nxt_bpt_tbp = (bpt_tbpif.taken_res == 2'b01) ? weakly_Pred1 : strongly_Pred1;
            end
            weakly_Pred1    : begin
                nxt_bpt_tbp = weakly_Pred1;
                if(bpt_tbpif.taken_res == 2'b10) nxt_bpt_tbp = strongly_Pred1;
                if(bpt_tbpif.taken_res == 2'b01) nxt_bpt_tbp = strongly_Pred0;
            end
            strongly_Pred0  : begin
                nxt_bpt_tbp = (bpt_tbpif.taken_res == 2'b10) ? weakly_Pred0 : strongly_Pred0;
            end
            weakly_Pred0    : begin
                nxt_bpt_tbp = weakly_Pred0;
                if(bpt_tbpif.taken_res == 2'b10) nxt_bpt_tbp = strongly_Pred1;
                if(bpt_tbpif.taken_res == 2'b01) nxt_bpt_tbp = strongly_Pred0;
            end
        endcase

    end

    always_ff @( posedge CLK, negedge nRST ) begin
        if(!nRST) begin
            bpt_tbp <= '0; 
        end
        else begin
            // Index into the bpt_tbp to update with state, using resolution PC to index
            if(bpt_tbpif.enable_res) begin
                bpt_tbp[bpt_tbpif.pc_res[((size-1)+2):2]] <= nxt_bpt_tbp;
            end
        end
    end
endmodule