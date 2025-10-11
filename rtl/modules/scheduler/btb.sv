`include "isa_types.vh"
`include "datapath_types.vh"
`include "btb_if.vh"

module btb #( 	
    parameter size = 11)
(
    input logic CLK, 
    input logic nRST, 
    btb_if.btb btbif
);
    //Internal Signals
    logic [((2**size)-1):0] [31:0] btb;

    //--------------Fetch Stage------------------
    //index into btb for branch target, using fetch PC
    assign btbif.bt_fetch = btb[btbif.pc_fetch[((size-1)+2):2]];

    //-------------Resolution Stage--------------
    always_ff @( posedge CLK, negedge nRST ) begin
        if(!nRST) begin
            btb <= '0;
        end
        else begin
            // Index into the btb to update with branch target, using resolution PC to index
            if(btbif.enable_res) begin
                btb[btbif.pc_res[((size-1)+2):2]] <= btbif.bt_res;
            end
        end
    end
endmodule