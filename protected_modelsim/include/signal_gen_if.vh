`ifndef SIGNAL_GEN_IF_VH
`define SIGNAL_GEN_IF_VH
`include "dram_pkg.vh"
`include "signal_gen_if.vh"

interface signal_gen_if ();
    import dram_pkg::*;

    //REFRESH request
    logic ref_re;

    //Signals interface between control unit and signal generator
    dram_state_t state, nstate; 
    logic [RANK_BITS-1:0] RA0;
    logic [BANK_GROUP_BITS-1:0] BG0;
    logic [BANK_BITS-1:0] BA0;
    logic [ROW_BITS-1:0] R0;
    logic [COLUMN_BITS-1:0] C0;

    //Interface between singal generator and DRAM
    logic ACT_n;
    logic RAS_n_A16;
    logic CAS_n_A15;
    logic WE_n_A14;
    logic ALERT_n;
    logic PARITY;
    logic RESET_n;
    logic TEN;
    logic CS_n;
    logic CKE;
    logic ODT;
    logic ZQ;
    logic PWR;
    logic VREF_CA;
    logic VREF_DQ;

    logic [RANK_BITS-1:0] C;
    logic [BANK_GROUP_BITS-1:0] BG;
    logic [BANK_BITS-1:0] BA;
    logic [ADDR_BITS-1:0] ADDR;
    logic ADDR_17;

    
    modport dut (
        input ref_re,
        input state, nstate, RA0, BG0, BA0, R0, C0,
        output ACT_n, RAS_n_A16, CAS_n_A15, WE_n_A14, ALERT_n, PARITY, RESET_n, TEN, CS_n, CKE, ODT, C, BG, BA, ADDR, ADDR_17, PWR, VREF_CA, VREF_DQ, ZQ
    );



endinterface

`endif