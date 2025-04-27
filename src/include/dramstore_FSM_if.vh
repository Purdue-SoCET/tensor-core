`ifndef  DRAMSTORE_FSM_IF_VH
`define DRAMSTORE_FSM_IF_VH
`include "sp_types_pkg.vh"
import sp_types_pkg::*;

interface dramstore_FSM_if;
    

    logic dramFIFO0_empty, dramFIFO1_empty, dramFIFO2_empty, dramFIFO3_empty, sStore_hit, dramFIFO0_REN, dramFIFO1_REN, dramFIFO2_REN, dramFIFO3_REN;
    logic sStore, s_Store, store_complete;
    logic [WORD_W-1:0] store_addr;
    logic [BITS_PER_ROW-1:0] store_data;
    dramFIFO_t dramFIFO0_rdata, dramFIFO1_rdata, dramFIFO2_rdata, dramFIFO3_rdata;

    modport sp (
        input dramFIFO0_empty, dramFIFO1_empty, dramFIFO2_empty, dramFIFO3_empty, sStore_hit, dramFIFO0_rdata, dramFIFO1_rdata, dramFIFO2_rdata, dramFIFO3_rdata,
        output dramFIFO0_REN, dramFIFO1_REN, dramFIFO2_REN, dramFIFO3_REN, sStore, store_addr, store_data, s_Store, store_complete
    );

endinterface

`endif 
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