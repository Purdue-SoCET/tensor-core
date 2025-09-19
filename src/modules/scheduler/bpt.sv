`include "isa_types.vh"
`include "datapath_types.vh"
`include "bpt_if.vh"

module bpt #( 	
    parameter size = 11)
(
    input logic CLK, 
    input logic nRST, 
    bpt_if.bpt bptif
);
    //Internal Signals
    localparam strongly_taken       = 2'b11; //upper bit 1 = taken
    localparam weakly_taken         = 2'b10;
    localparam strongly_not_taken   = 2'b00; //upper bit 0 = not taken
    localparam weakly_not_taken     = 2'b01;

    logic [((2**size)-1):0] [1:0] bpt;

    logic [1:0] curr_bpt, nxt_bpt;

    //--------------Fetch Stage------------------
    //index into bpt for branch target, using fetch PC (Upper bit gives prediction)
    assign bptif.pred_fetch = bpt[bptif.pc_fetch[((size-1)+2):2]][1];

    //-------------Resolution Stage--------------
    //index into bpt from resolution state to find current state
    assign curr_bpt = bpt[bptif.pc_res[((size-1)+2):2]];

    //check if prediction was correct by comparing upper bit of current state and taken from resolution
    assign bptif.pred_correct = (curr_bpt[1] == bptif.taken_res);

    always_comb begin
        nxt_bpt = curr_bpt;
        casez(curr_bpt)
            strongly_taken      : nxt_bpt = (bptif.taken_res) ? strongly_taken    : weakly_taken;
            weakly_taken        : nxt_bpt = (bptif.taken_res) ? strongly_taken    : strongly_not_taken;
            strongly_not_taken  : nxt_bpt = (bptif.taken_res) ? weakly_not_taken  : strongly_not_taken;
            weakly_not_taken    : nxt_bpt = (bptif.taken_res) ? strongly_taken    : strongly_not_taken;
        endcase

    end

    always_ff @( posedge CLK, negedge nRST ) begin
        if(!nRST) begin
            bpt <= '0; 
        end
        else begin
            // Index into the bpt to update with state, using resolution PC to index
            if(bptif.enable_res) begin
                bpt[bptif.pc_res[((size-1)+2):2]] <= nxt_bpt;
            end
        end
    end
endmodule