`include "isa_types.vh"
`include "datapath_types.vh"
`include "btb_if.vh"

module nbit_stp_shiftreg #( 	
    parameter size = 3)
(
    input logic CLK, 
    input logic nRST, 
    input logic enable,
    input logic in,
    output logic [(size-1):0] out
);
    always_ff @( posedge CLK, negedge nRST ) begin
        if(!nRST) begin
            out <= '0;
        end
        else if (enable) begin
            out <= {out[(size-1):0], in};
        end
    end
endmodule