`include "types_pkg.vh"
`include "dramstore_FSM_if.vh"
import types_pkg::*;

module dramstore_FSM (
    input logic CLK, nRST,
    dramstore_FSM_if.sp spif
);

    always_comb begin
        spif.sStore = 1'b0; //~(spif.dramFIFO0_empty && spif.dramFIFO1_empty && spif.dramFIFO2_empty && spif.dramFIFO3_empty);
        spif.dramFIFO0_REN = 1'b0;
        spif.dramFIFO1_REN = 1'b0;
        spif.dramFIFO2_REN = 1'b0;
        spif.dramFIFO3_REN = 1'b0;
        spif.store_addr = '0;
        spif.store_data = '0;
        if (spif.dramFIFO0_empty == 1'b0) begin
            spif.dramFIFO0_REN = spif.sStore_hit;
            spif.store_addr = spif.dramFIFO0_rdata[99:68] + (STRIDE * spif.dramFIFO0_rdata[65:64]);
            spif.store_data = spif.dramFIFO0_rdata[63:0];
            spif.sStore = 1'b1;
        end
        else if (spif.dramFIFO1_empty == 1'b0) begin
            spif.dramFIFO1_REN = spif.sStore_hit;
            spif.store_addr = spif.dramFIFO1_rdata[99:68] + (STRIDE * spif.dramFIFO0_rdata[65:64]);
            spif.store_data = spif.dramFIFO1_rdata[63:0];
            spif.sStore = 1'b1;
        end
        else if (spif.dramFIFO2_empty == 1'b0) begin
            spif.dramFIFO2_REN = spif.sStore_hit;
            spif.store_addr = spif.dramFIFO2_rdata[99:68] + (STRIDE * spif.dramFIFO0_rdata[65:64]);
            spif.store_data = spif.dramFIFO2_rdata[63:0];
            spif.sStore = 1'b1;
        end
        else if (spif.dramFIFO3_empty == 1'b0) begin
            spif.dramFIFO3_REN = spif.sStore_hit;
            spif.store_addr = spif.dramFIFO3_rdata[99:68] + (STRIDE * spif.dramFIFO0_rdata[65:64]);
            spif.store_data = spif.dramFIFO3_rdata[63:0];
            spif.sStore = 1'b1;
        end
    end
endmodule
/*
Inputs:
dramFIFO0_empty
dramFIFO1_empty
dramFIFO2_empty
dramFIFO3_empty
dramFIFO0_rdata
dramFIFO1_rdata
dramFIFO2_rdata
dramFIFO3_rdata
sStore_hit

Outputs:
dramFIFO0_REN
dramFIFO1_REN
dramFIFO2_REN
dramFIFO3_REN
sStore
store_addr
store_data


*/