// MICRON TECHNOLOGY, INC. - CONFIDENTIAL AND PROPRIETARY INFORMATION
interface DDR4_if #(parameter CONFIGURED_DQ_BITS = 8) ();
    timeunit 1ps;
    timeprecision 1ps;
    import arch_package::*;
    parameter CONFIGURED_DQS_BITS = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_DM_BITS = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    logic[1:0] CK; // CK[0]==CK_c CK[1]==CK_t
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
    logic[MAX_RANK_BITS-1:0] C;
    logic[MAX_BANK_GROUP_BITS-1:0] BG;
    logic[MAX_BANK_BITS-1:0] BA;
    logic[13:0] ADDR;
    logic ADDR_17;
    wire[CONFIGURED_DM_BITS-1:0] DM_n;
    wire[CONFIGURED_DQ_BITS-1:0] DQ;
    wire[CONFIGURED_DQS_BITS-1:0] DQS_t;
    wire[CONFIGURED_DQS_BITS-1:0] DQS_c;
    logic ZQ;
    logic PWR;
    logic VREF_CA;
    logic VREF_DQ;
endinterface

interface ddr4_module_if;
    timeunit 1ps;
    timeprecision 1ps;
    import arch_package::*;
    `include "dimm.vh"
    
    logic[1:0] CK; // CK[0]==CK_c CK[1]==CK_t
    logic ACT_n;
    logic RAS_n_A16;
    logic CAS_n_A15;
    logic WE_n_A14;
    logic ALERT_n;
    logic PARITY;
    logic RESET_n;
    logic TEN;
    logic[MAX_DIMM_CS_BITS-1:0] CS_n;
    logic CKE;
    logic ODT;
    logic[MAX_RANK_BITS-1:0] C;
    logic[MAX_BANK_GROUP_BITS-1:0] BG;
    logic[MAX_BANK_BITS-1:0] BA;
    logic[13:0] ADDR;
    logic ADDR_17;
    logic ZQ;
    logic PWR;
    logic VREF_CA;
    logic VREF_DQ;
    wire[MAX_DIMM_DQ_BITS-1:0] DQ;
    wire[MAX_DIMM_DQS_BITS-1:0] DQS_t;
    wire[MAX_DIMM_DQS_BITS-1:0] DQS_c;
    wire[MAX_DIMM_DM_BITS-1:0] DM_n;
    
`ifdef DDR4_X16
    "DDR4 modules with x16 components are not available and this code will not compile or run."
`endif
    `ifdef DDR4_X4
        parameter int CONFIGURED_DQ_BITS = 4;
    `endif
    `ifdef DDR4_X8
        parameter int CONFIGURED_DQ_BITS = 8;
    `endif
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u0_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u1_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u2_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u3_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u4_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u5_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u6_r0();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u7_r0();
    `ifdef ECC
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u8_r0();
    `endif
    `ifdef DDR4_X4
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u9_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u10_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u11_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u12_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u13_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u14_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u15_r0();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u16_r0();
        `ifdef ECC
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u17_r0();
        `endif
    `endif
    `ifdef DUAL_RANK
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u18_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u19_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u20_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u21_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u22_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u23_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u24_r1();
        DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u25_r1();
        `ifdef ECC
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u26_r1();
        `endif
        `ifdef DDR4_X4
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u27_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u28_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u29_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u30_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u31_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u32_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u33_r1();
            DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u34_r1();
            `ifdef ECC
                DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) u35_r1();
            `endif
        `endif
    `endif
    
    // Controller outputs
    assign {u7_r0.CK,u6_r0.CK,u5_r0.CK,u4_r0.CK,u3_r0.CK,u2_r0.CK,u1_r0.CK,u0_r0.CK} = {CK,CK,CK,CK,CK,CK,CK,CK};
    assign {u7_r0.ACT_n,u6_r0.ACT_n,u5_r0.ACT_n,u4_r0.ACT_n,u3_r0.ACT_n,u2_r0.ACT_n,u1_r0.ACT_n,u0_r0.ACT_n} = {ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n};
    assign {u7_r0.RAS_n_A16,u6_r0.RAS_n_A16,u5_r0.RAS_n_A16,u4_r0.RAS_n_A16,u3_r0.RAS_n_A16,u2_r0.RAS_n_A16,u1_r0.RAS_n_A16,u0_r0.RAS_n_A16} = {RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16};
    assign {u7_r0.CAS_n_A15,u6_r0.CAS_n_A15,u5_r0.CAS_n_A15,u4_r0.CAS_n_A15,u3_r0.CAS_n_A15,u2_r0.CAS_n_A15,u1_r0.CAS_n_A15,u0_r0.CAS_n_A15} = {CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15};
    assign {u7_r0.WE_n_A14,u6_r0.WE_n_A14,u5_r0.WE_n_A14,u4_r0.WE_n_A14,u3_r0.WE_n_A14,u2_r0.WE_n_A14,u1_r0.WE_n_A14,u0_r0.WE_n_A14} = {WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14};
    assign {u7_r0.PARITY,u6_r0.PARITY,u5_r0.PARITY,u4_r0.PARITY,u3_r0.PARITY,u2_r0.PARITY,u1_r0.PARITY,u0_r0.PARITY} = {PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY};
    assign {u7_r0.RESET_n,u6_r0.RESET_n,u5_r0.RESET_n,u4_r0.RESET_n,u3_r0.RESET_n,u2_r0.RESET_n,u1_r0.RESET_n,u0_r0.RESET_n} = {RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n};
    assign {u7_r0.TEN,u6_r0.TEN,u5_r0.TEN,u4_r0.TEN,u3_r0.TEN,u2_r0.TEN,u1_r0.TEN,u0_r0.TEN} = {TEN,TEN,TEN,TEN,TEN,TEN,TEN,TEN};
    assign {u7_r0.CKE,u6_r0.CKE,u5_r0.CKE,u4_r0.CKE,u3_r0.CKE,u2_r0.CKE,u1_r0.CKE,u0_r0.CKE} = {CKE,CKE,CKE,CKE,CKE,CKE,CKE,CKE};
    assign {u7_r0.ODT,u6_r0.ODT,u5_r0.ODT,u4_r0.ODT,u3_r0.ODT,u2_r0.ODT,u1_r0.ODT,u0_r0.ODT} = {ODT,ODT,ODT,ODT,ODT,ODT,ODT,ODT};
    assign {u7_r0.C,u6_r0.C,u5_r0.C,u4_r0.C,u3_r0.C,u2_r0.C,u1_r0.C,u0_r0.C} = {C,C,C,C,C,C,C,C};
    assign {u7_r0.BG,u6_r0.BG,u5_r0.BG,u4_r0.BG,u3_r0.BG,u2_r0.BG,u1_r0.BG,u0_r0.BG} = {BG,BG,BG,BG,BG,BG,BG,BG};
    assign {u7_r0.BA,u6_r0.BA,u5_r0.BA,u4_r0.BA,u3_r0.BA,u2_r0.BA,u1_r0.BA,u0_r0.BA} = {BA,BA,BA,BA,BA,BA,BA,BA};
    assign {u7_r0.ADDR,u6_r0.ADDR,u5_r0.ADDR,u4_r0.ADDR,u3_r0.ADDR,u2_r0.ADDR,u1_r0.ADDR,u0_r0.ADDR} = {ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR};
    assign {u7_r0.ADDR_17,u6_r0.ADDR_17,u5_r0.ADDR_17,u4_r0.ADDR_17,u3_r0.ADDR_17,u2_r0.ADDR_17,u1_r0.ADDR_17,u0_r0.ADDR_17} = {ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17};
    assign {u7_r0.ZQ,u6_r0.ZQ,u5_r0.ZQ,u4_r0.ZQ,u3_r0.ZQ,u2_r0.ZQ,u1_r0.ZQ,u0_r0.ZQ} = {ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ};
    assign {u7_r0.PWR,u6_r0.PWR,u5_r0.PWR,u4_r0.PWR,u3_r0.PWR,u2_r0.PWR,u1_r0.PWR,u0_r0.PWR} = {PWR,PWR,PWR,PWR,PWR,PWR,PWR,PWR};
    assign {u7_r0.VREF_CA,u6_r0.VREF_CA,u5_r0.VREF_CA,u4_r0.VREF_CA,u3_r0.VREF_CA,u2_r0.VREF_CA,u1_r0.VREF_CA,u0_r0.VREF_CA} = {VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA};
    assign {u7_r0.VREF_DQ,u6_r0.VREF_DQ,u5_r0.VREF_DQ,u4_r0.VREF_DQ,u3_r0.VREF_DQ,u2_r0.VREF_DQ,u1_r0.VREF_DQ,u0_r0.VREF_DQ} = {VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ};
    assign {u7_r0.CS_n,u6_r0.CS_n,u5_r0.CS_n,u4_r0.CS_n,u3_r0.CS_n,u2_r0.CS_n,u1_r0.CS_n,u0_r0.CS_n} = {CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0]};
    `ifdef ECC
        assign {u8_r0.CK} = {CK};
        assign {u8_r0.ACT_n} = {ACT_n};
        assign {u8_r0.RAS_n_A16} = {RAS_n_A16};
        assign {u8_r0.CAS_n_A15} = {CAS_n_A15};
        assign {u8_r0.WE_n_A14} = {WE_n_A14};
        assign {u8_r0.PARITY} = {PARITY};
        assign {u8_r0.RESET_n} = {RESET_n};
        assign {u8_r0.TEN} = {TEN};
        assign {u8_r0.CKE} = {CKE};
        assign {u8_r0.ODT} = {ODT};
        assign {u8_r0.C} = {C};
        assign {u8_r0.BG} = {BG};
        assign {u8_r0.BA} = {BA};
        assign {u8_r0.ADDR} = {ADDR};
        assign {u8_r0.ADDR_17} = {ADDR_17};
        assign {u8_r0.ZQ} = {ZQ};
        assign {u8_r0.PWR} = {PWR};
        assign {u8_r0.VREF_CA} = {VREF_CA};
        assign {u8_r0.VREF_DQ} = {VREF_DQ};
        assign {u8_r0.CS_n} = {CS_n[0]};
    `endif
    `ifdef DDR4_X4
        assign {u16_r0.CK,u15_r0.CK,u14_r0.CK,u13_r0.CK,u12_r0.CK,u11_r0.CK,u10_r0.CK,u9_r0.CK} = {CK,CK,CK,CK,CK,CK,CK,CK};
        assign {u16_r0.ACT_n,u15_r0.ACT_n,u14_r0.ACT_n,u13_r0.ACT_n,u12_r0.ACT_n,u11_r0.ACT_n,u10_r0.ACT_n,u9_r0.ACT_n} = {ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n};
        assign {u16_r0.RAS_n_A16,u15_r0.RAS_n_A16,u14_r0.RAS_n_A16,u13_r0.RAS_n_A16,u12_r0.RAS_n_A16,u11_r0.RAS_n_A16,u10_r0.RAS_n_A16,u9_r0.RAS_n_A16} = {RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16};
        assign {u16_r0.CAS_n_A15,u15_r0.CAS_n_A15,u14_r0.CAS_n_A15,u13_r0.CAS_n_A15,u12_r0.CAS_n_A15,u11_r0.CAS_n_A15,u10_r0.CAS_n_A15,u9_r0.CAS_n_A15} = {CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15};
        assign {u16_r0.WE_n_A14,u15_r0.WE_n_A14,u14_r0.WE_n_A14,u13_r0.WE_n_A14,u12_r0.WE_n_A14,u11_r0.WE_n_A14,u10_r0.WE_n_A14,u9_r0.WE_n_A14} = {WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14};
        assign {u16_r0.PARITY,u15_r0.PARITY,u14_r0.PARITY,u13_r0.PARITY,u12_r0.PARITY,u11_r0.PARITY,u10_r0.PARITY,u9_r0.PARITY} = {PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY};
        assign {u16_r0.RESET_n,u15_r0.RESET_n,u14_r0.RESET_n,u13_r0.RESET_n,u12_r0.RESET_n,u11_r0.RESET_n,u10_r0.RESET_n,u9_r0.RESET_n} = {RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n};
        assign {u16_r0.TEN,u15_r0.TEN,u14_r0.TEN,u13_r0.TEN,u12_r0.TEN,u11_r0.TEN,u10_r0.TEN,u9_r0.TEN} = {TEN,TEN,TEN,TEN,TEN,TEN,TEN,TEN};
        assign {u16_r0.CKE,u15_r0.CKE,u14_r0.CKE,u13_r0.CKE,u12_r0.CKE,u11_r0.CKE,u10_r0.CKE,u9_r0.CKE} = {CKE,CKE,CKE,CKE,CKE,CKE,CKE,CKE};
        assign {u16_r0.ODT,u15_r0.ODT,u14_r0.ODT,u13_r0.ODT,u12_r0.ODT,u11_r0.ODT,u10_r0.ODT,u9_r0.ODT} = {ODT,ODT,ODT,ODT,ODT,ODT,ODT,ODT};
        assign {u16_r0.C,u15_r0.C,u14_r0.C,u13_r0.C,u12_r0.C,u11_r0.C,u10_r0.C,u9_r0.C} = {C,C,C,C,C,C,C,C};
        assign {u16_r0.BG,u15_r0.BG,u14_r0.BG,u13_r0.BG,u12_r0.BG,u11_r0.BG,u10_r0.BG,u9_r0.BG} = {BG,BG,BG,BG,BG,BG,BG,BG};
        assign {u16_r0.BA,u15_r0.BA,u14_r0.BA,u13_r0.BA,u12_r0.BA,u11_r0.BA,u10_r0.BA,u9_r0.BA} = {BA,BA,BA,BA,BA,BA,BA,BA};
        assign {u16_r0.ADDR,u15_r0.ADDR,u14_r0.ADDR,u13_r0.ADDR,u12_r0.ADDR,u11_r0.ADDR,u10_r0.ADDR,u9_r0.ADDR} = {ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR};
        assign {u16_r0.ADDR_17,u15_r0.ADDR_17,u14_r0.ADDR_17,u13_r0.ADDR_17,u12_r0.ADDR_17,u11_r0.ADDR_17,u10_r0.ADDR_17,u9_r0.ADDR_17} = {ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17};
        assign {u16_r0.ZQ,u15_r0.ZQ,u14_r0.ZQ,u13_r0.ZQ,u12_r0.ZQ,u11_r0.ZQ,u10_r0.ZQ,u9_r0.ZQ} = {ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ};
        assign {u16_r0.PWR,u15_r0.PWR,u14_r0.PWR,u13_r0.PWR,u12_r0.PWR,u11_r0.PWR,u10_r0.PWR,u9_r0.PWR} = {PWR,PWR,PWR,PWR,PWR,PWR,PWR,PWR};
        assign {u16_r0.VREF_CA,u15_r0.VREF_CA,u14_r0.VREF_CA,u13_r0.VREF_CA,u12_r0.VREF_CA,u11_r0.VREF_CA,u10_r0.VREF_CA,u9_r0.VREF_CA} = {VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA};
        assign {u16_r0.VREF_DQ,u15_r0.VREF_DQ,u14_r0.VREF_DQ,u13_r0.VREF_DQ,u12_r0.VREF_DQ,u11_r0.VREF_DQ,u10_r0.VREF_DQ,u9_r0.VREF_DQ} = {VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ};
        assign {u16_r0.CS_n,u15_r0.CS_n,u14_r0.CS_n,u13_r0.CS_n,u12_r0.CS_n,u11_r0.CS_n,u10_r0.CS_n,u9_r0.CS_n} = {CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0],CS_n[0]};
        `ifdef ECC
            assign {u17_r0.CK} = {CK};
            assign {u17_r0.ACT_n} = {ACT_n};
            assign {u17_r0.RAS_n_A16} = {RAS_n_A16};
            assign {u17_r0.CAS_n_A15} = {CAS_n_A15};
            assign {u17_r0.WE_n_A14} = {WE_n_A14};
            assign {u17_r0.PARITY} = {PARITY};
            assign {u17_r0.RESET_n} = {RESET_n};
            assign {u17_r0.TEN} = {TEN};
            assign {u17_r0.CKE} = {CKE};
            assign {u17_r0.ODT} = {ODT};
            assign {u17_r0.C} = {C};
            assign {u17_r0.BG} = {BG};
            assign {u17_r0.BA} = {BA};
            assign {u17_r0.ADDR} = {ADDR};
            assign {u17_r0.ADDR_17} = {ADDR_17};
            assign {u17_r0.ZQ} = {ZQ};
            assign {u17_r0.PWR} = {PWR};
            assign {u17_r0.VREF_CA} = {VREF_CA};
            assign {u17_r0.VREF_DQ} = {VREF_DQ};
            assign {u17_r0.CS_n} = {CS_n[0]};
        `endif
    `endif
    `ifdef DUAL_RANK
        assign {u25_r1.CK,u24_r1.CK,u23_r1.CK,u22_r1.CK,u21_r1.CK,u20_r1.CK,u19_r1.CK,u18_r1.CK} = {CK,CK,CK,CK,CK,CK,CK,CK};
        assign {u25_r1.ACT_n,u24_r1.ACT_n,u23_r1.ACT_n,u22_r1.ACT_n,u21_r1.ACT_n,u20_r1.ACT_n,u19_r1.ACT_n,u18_r1.ACT_n} = {ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n};
        assign {u25_r1.RAS_n_A16,u24_r1.RAS_n_A16,u23_r1.RAS_n_A16,u22_r1.RAS_n_A16,u21_r1.RAS_n_A16,u20_r1.RAS_n_A16,u19_r1.RAS_n_A16,u18_r1.RAS_n_A16} = {RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16};
        assign {u25_r1.CAS_n_A15,u24_r1.CAS_n_A15,u23_r1.CAS_n_A15,u22_r1.CAS_n_A15,u21_r1.CAS_n_A15,u20_r1.CAS_n_A15,u19_r1.CAS_n_A15,u18_r1.CAS_n_A15} = {CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15};
        assign {u25_r1.WE_n_A14,u24_r1.WE_n_A14,u23_r1.WE_n_A14,u22_r1.WE_n_A14,u21_r1.WE_n_A14,u20_r1.WE_n_A14,u19_r1.WE_n_A14,u18_r1.WE_n_A14} = {WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14};
        assign {u25_r1.PARITY,u24_r1.PARITY,u23_r1.PARITY,u22_r1.PARITY,u21_r1.PARITY,u20_r1.PARITY,u19_r1.PARITY,u18_r1.PARITY} = {PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY};
        assign {u25_r1.RESET_n,u24_r1.RESET_n,u23_r1.RESET_n,u22_r1.RESET_n,u21_r1.RESET_n,u20_r1.RESET_n,u19_r1.RESET_n,u18_r1.RESET_n} = {RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n};
        assign {u25_r1.TEN,u24_r1.TEN,u23_r1.TEN,u22_r1.TEN,u21_r1.TEN,u20_r1.TEN,u19_r1.TEN,u18_r1.TEN} = {TEN,TEN,TEN,TEN,TEN,TEN,TEN,TEN};
        assign {u25_r1.CKE,u24_r1.CKE,u23_r1.CKE,u22_r1.CKE,u21_r1.CKE,u20_r1.CKE,u19_r1.CKE,u18_r1.CKE} = {CKE,CKE,CKE,CKE,CKE,CKE,CKE,CKE};
        assign {u25_r1.ODT,u24_r1.ODT,u23_r1.ODT,u22_r1.ODT,u21_r1.ODT,u20_r1.ODT,u19_r1.ODT,u18_r1.ODT} = {ODT,ODT,ODT,ODT,ODT,ODT,ODT,ODT};
        assign {u25_r1.C,u24_r1.C,u23_r1.C,u22_r1.C,u21_r1.C,u20_r1.C,u19_r1.C,u18_r1.C} = {C,C,C,C,C,C,C,C};
        assign {u25_r1.BG,u24_r1.BG,u23_r1.BG,u22_r1.BG,u21_r1.BG,u20_r1.BG,u19_r1.BG,u18_r1.BG} = {BG,BG,BG,BG,BG,BG,BG,BG};
        assign {u25_r1.BA,u24_r1.BA,u23_r1.BA,u22_r1.BA,u21_r1.BA,u20_r1.BA,u19_r1.BA,u18_r1.BA} = {BA,BA,BA,BA,BA,BA,BA,BA};
        assign {u25_r1.ADDR,u24_r1.ADDR,u23_r1.ADDR,u22_r1.ADDR,u21_r1.ADDR,u20_r1.ADDR,u19_r1.ADDR,u18_r1.ADDR} = {ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR};
        assign {u25_r1.ADDR_17,u24_r1.ADDR_17,u23_r1.ADDR_17,u22_r1.ADDR_17,u21_r1.ADDR_17,u20_r1.ADDR_17,u19_r1.ADDR_17,u18_r1.ADDR_17} = {ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17};
        assign {u25_r1.ZQ,u24_r1.ZQ,u23_r1.ZQ,u22_r1.ZQ,u21_r1.ZQ,u20_r1.ZQ,u19_r1.ZQ,u18_r1.ZQ} = {ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ};
        assign {u25_r1.PWR,u24_r1.PWR,u23_r1.PWR,u22_r1.PWR,u21_r1.PWR,u20_r1.PWR,u19_r1.PWR,u18_r1.PWR} = {PWR,PWR,PWR,PWR,PWR,PWR,PWR,PWR};
        assign {u25_r1.VREF_CA,u24_r1.VREF_CA,u23_r1.VREF_CA,u22_r1.VREF_CA,u21_r1.VREF_CA,u20_r1.VREF_CA,u19_r1.VREF_CA,u18_r1.VREF_CA} = {VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA};
        assign {u25_r1.VREF_DQ,u24_r1.VREF_DQ,u23_r1.VREF_DQ,u22_r1.VREF_DQ,u21_r1.VREF_DQ,u20_r1.VREF_DQ,u19_r1.VREF_DQ,u18_r1.VREF_DQ} = {VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ};
        assign {u25_r1.CS_n,u24_r1.CS_n,u23_r1.CS_n,u22_r1.CS_n,u21_r1.CS_n,u20_r1.CS_n,u19_r1.CS_n,u18_r1.CS_n} = {CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1]};
        `ifdef ECC
            assign {u26_r1.CK} = {CK};
            assign {u26_r1.ACT_n} = {ACT_n};
            assign {u26_r1.RAS_n_A16} = {RAS_n_A16};
            assign {u26_r1.CAS_n_A15} = {CAS_n_A15};
            assign {u26_r1.WE_n_A14} = {WE_n_A14};
            assign {u26_r1.PARITY} = {PARITY};
            assign {u26_r1.RESET_n} = {RESET_n};
            assign {u26_r1.TEN} = {TEN};
            assign {u26_r1.CKE} = {CKE};
            assign {u26_r1.ODT} = {ODT};
            assign {u26_r1.C} = {C};
            assign {u26_r1.BG} = {BG};
            assign {u26_r1.BA} = {BA};
            assign {u26_r1.ADDR} = {ADDR};
            assign {u26_r1.ADDR_17} = {ADDR_17};
            assign {u26_r1.ZQ} = {ZQ};
            assign {u26_r1.PWR} = {PWR};
            assign {u26_r1.VREF_CA} = {VREF_CA};
            assign {u26_r1.VREF_DQ} = {VREF_DQ};
            assign {u26_r1.CS_n} = {CS_n[1]};
        `endif
        `ifdef DDR4_X4
            assign {u34_r1.CK,u33_r1.CK,u32_r1.CK,u31_r1.CK,u30_r1.CK,u29_r1.CK,u28_r1.CK,u27_r1.CK} = {CK,CK,CK,CK,CK,CK,CK,CK};
            assign {u34_r1.ACT_n,u33_r1.ACT_n,u32_r1.ACT_n,u31_r1.ACT_n,u30_r1.ACT_n,u29_r1.ACT_n,u28_r1.ACT_n,u27_r1.ACT_n} = {ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n,ACT_n};
            assign {u34_r1.RAS_n_A16,u33_r1.RAS_n_A16,u32_r1.RAS_n_A16,u31_r1.RAS_n_A16,u30_r1.RAS_n_A16,u29_r1.RAS_n_A16,u28_r1.RAS_n_A16,u27_r1.RAS_n_A16} = {RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16,RAS_n_A16};
            assign {u34_r1.CAS_n_A15,u33_r1.CAS_n_A15,u32_r1.CAS_n_A15,u31_r1.CAS_n_A15,u30_r1.CAS_n_A15,u29_r1.CAS_n_A15,u28_r1.CAS_n_A15,u27_r1.CAS_n_A15} = {CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15,CAS_n_A15};
            assign {u34_r1.WE_n_A14,u33_r1.WE_n_A14,u32_r1.WE_n_A14,u31_r1.WE_n_A14,u30_r1.WE_n_A14,u29_r1.WE_n_A14,u28_r1.WE_n_A14,u27_r1.WE_n_A14} = {WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14,WE_n_A14};
            assign {u34_r1.PARITY,u33_r1.PARITY,u32_r1.PARITY,u31_r1.PARITY,u30_r1.PARITY,u29_r1.PARITY,u28_r1.PARITY,u27_r1.PARITY} = {PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY,PARITY};
            assign {u34_r1.RESET_n,u33_r1.RESET_n,u32_r1.RESET_n,u31_r1.RESET_n,u30_r1.RESET_n,u29_r1.RESET_n,u28_r1.RESET_n,u27_r1.RESET_n} = {RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n,RESET_n};
            assign {u34_r1.TEN,u33_r1.TEN,u32_r1.TEN,u31_r1.TEN,u30_r1.TEN,u29_r1.TEN,u28_r1.TEN,u27_r1.TEN} = {TEN,TEN,TEN,TEN,TEN,TEN,TEN,TEN};
            assign {u34_r1.CKE,u33_r1.CKE,u32_r1.CKE,u31_r1.CKE,u30_r1.CKE,u29_r1.CKE,u28_r1.CKE,u27_r1.CKE} = {CKE,CKE,CKE,CKE,CKE,CKE,CKE,CKE};
            assign {u34_r1.ODT,u33_r1.ODT,u32_r1.ODT,u31_r1.ODT,u30_r1.ODT,u29_r1.ODT,u28_r1.ODT,u27_r1.ODT} = {ODT,ODT,ODT,ODT,ODT,ODT,ODT,ODT};
            assign {u34_r1.C,u33_r1.C,u32_r1.C,u31_r1.C,u30_r1.C,u29_r1.C,u28_r1.C,u27_r1.C} = {C,C,C,C,C,C,C,C};
            assign {u34_r1.BG,u33_r1.BG,u32_r1.BG,u31_r1.BG,u30_r1.BG,u29_r1.BG,u28_r1.BG,u27_r1.BG} = {BG,BG,BG,BG,BG,BG,BG,BG};
            assign {u34_r1.BA,u33_r1.BA,u32_r1.BA,u31_r1.BA,u30_r1.BA,u29_r1.BA,u28_r1.BA,u27_r1.BA} = {BA,BA,BA,BA,BA,BA,BA,BA};
            assign {u34_r1.ADDR,u33_r1.ADDR,u32_r1.ADDR,u31_r1.ADDR,u30_r1.ADDR,u29_r1.ADDR,u28_r1.ADDR,u27_r1.ADDR} = {ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR,ADDR};
            assign {u34_r1.ADDR_17,u33_r1.ADDR_17,u32_r1.ADDR_17,u31_r1.ADDR_17,u30_r1.ADDR_17,u29_r1.ADDR_17,u28_r1.ADDR_17,u27_r1.ADDR_17} = {ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17,ADDR_17};
            assign {u34_r1.ZQ,u33_r1.ZQ,u32_r1.ZQ,u31_r1.ZQ,u30_r1.ZQ,u29_r1.ZQ,u28_r1.ZQ,u27_r1.ZQ} = {ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ,ZQ};
            assign {u34_r1.PWR,u33_r1.PWR,u32_r1.PWR,u31_r1.PWR,u30_r1.PWR,u29_r1.PWR,u28_r1.PWR,u27_r1.PWR} = {PWR,PWR,PWR,PWR,PWR,PWR,PWR,PWR};
            assign {u34_r1.VREF_CA,u33_r1.VREF_CA,u32_r1.VREF_CA,u31_r1.VREF_CA,u30_r1.VREF_CA,u29_r1.VREF_CA,u28_r1.VREF_CA,u27_r1.VREF_CA} = {VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA,VREF_CA};
            assign {u34_r1.VREF_DQ,u33_r1.VREF_DQ,u32_r1.VREF_DQ,u31_r1.VREF_DQ,u30_r1.VREF_DQ,u29_r1.VREF_DQ,u28_r1.VREF_DQ,u27_r1.VREF_DQ} = {VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ,VREF_DQ};
            assign {u34_r1.CS_n,u33_r1.CS_n,u32_r1.CS_n,u31_r1.CS_n,u30_r1.CS_n,u29_r1.CS_n,u28_r1.CS_n,u27_r1.CS_n} = {CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1],CS_n[1]};
            `ifdef ECC
                assign {u35_r1.CK} = {CK};
                assign {u35_r1.ACT_n} = {ACT_n};
                assign {u35_r1.RAS_n_A16} = {RAS_n_A16};
                assign {u35_r1.CAS_n_A15} = {CAS_n_A15};
                assign {u35_r1.WE_n_A14} = {WE_n_A14};
                assign {u35_r1.PARITY} = {PARITY};
                assign {u35_r1.RESET_n} = {RESET_n};
                assign {u35_r1.TEN} = {TEN};
                assign {u35_r1.CKE} = {CKE};
                assign {u35_r1.ODT} = {ODT};
                assign {u35_r1.C} = {C};
                assign {u35_r1.BG} = {BG};
                assign {u35_r1.BA} = {BA};
                assign {u35_r1.ADDR} = {ADDR};
                assign {u35_r1.ADDR_17} = {ADDR_17};
                assign {u35_r1.ZQ} = {ZQ};
                assign {u35_r1.PWR} = {PWR};
                assign {u35_r1.VREF_CA} = {VREF_CA};
                assign {u35_r1.VREF_DQ} = {VREF_DQ};
                assign {u35_r1.CS_n} = {CS_n[1]};
            `endif
        `endif
    `endif
    
    `ifdef DDR4_X8
        `ifdef ECC
            // Bidirectional connections
            assign DQ = {u8_r0.DQ,u7_r0.DQ,u6_r0.DQ,u5_r0.DQ,u4_r0.DQ,u3_r0.DQ,u2_r0.DQ,u1_r0.DQ,u0_r0.DQ};
            assign DM_n = {u8_r0.DM_n,u7_r0.DM_n,u6_r0.DM_n,u5_r0.DM_n,u4_r0.DM_n,u3_r0.DM_n,u2_r0.DM_n,u1_r0.DM_n,u0_r0.DM_n};
            assign DQS_t = {u8_r0.DQS_t,u7_r0.DQS_t,u6_r0.DQS_t,u5_r0.DQS_t,u4_r0.DQS_t,u3_r0.DQS_t,u2_r0.DQS_t,u1_r0.DQS_t,u0_r0.DQS_t};
            assign DQS_c = {u8_r0.DQS_c,u7_r0.DQS_c,u6_r0.DQS_c,u5_r0.DQS_c,u4_r0.DQS_c,u3_r0.DQS_c,u2_r0.DQS_c,u1_r0.DQS_c,u0_r0.DQS_c};
            // Controller inputs
            always @(u0_r0.ALERT_n | u1_r0.ALERT_n | u2_r0.ALERT_n | u3_r0.ALERT_n | u4_r0.ALERT_n | u5_r0.ALERT_n | u6_r0.ALERT_n | u7_r0.ALERT_n | u8_r0.ALERT_n) begin
                ALERT_n = u0_r0.ALERT_n & u1_r0.ALERT_n & u2_r0.ALERT_n & u3_r0.ALERT_n & u4_r0.ALERT_n & u5_r0.ALERT_n & u6_r0.ALERT_n & u7_r0.ALERT_n & u8_r0.ALERT_n;
            end
        `else
            // Bidirectional connections
            assign DQ = {u7_r0.DQ,u6_r0.DQ,u5_r0.DQ,u4_r0.DQ,u3_r0.DQ,u2_r0.DQ,u1_r0.DQ,u0_r0.DQ};
            assign DM_n = {u7_r0.DM_n,u6_r0.DM_n,u5_r0.DM_n,u4_r0.DM_n,u3_r0.DM_n,u2_r0.DM_n,u1_r0.DM_n,u0_r0.DM_n};
            assign DQS_t = {u7_r0.DQS_t,u6_r0.DQS_t,u5_r0.DQS_t,u4_r0.DQS_t,u3_r0.DQS_t,u2_r0.DQS_t,u1_r0.DQS_t,u0_r0.DQS_t};
            assign DQS_c = {u7_r0.DQS_c,u6_r0.DQS_c,u5_r0.DQS_c,u4_r0.DQS_c,u3_r0.DQS_c,u2_r0.DQS_c,u1_r0.DQS_c,u0_r0.DQS_c};
            // Controller inputs
            always @(u0_r0.ALERT_n | u1_r0.ALERT_n | u2_r0.ALERT_n | u3_r0.ALERT_n | u4_r0.ALERT_n | u5_r0.ALERT_n | u6_r0.ALERT_n | u7_r0.ALERT_n) begin
                ALERT_n = u0_r0.ALERT_n & u1_r0.ALERT_n & u2_r0.ALERT_n & u3_r0.ALERT_n & u4_r0.ALERT_n & u5_r0.ALERT_n & u6_r0.ALERT_n & u7_r0.ALERT_n;
            end
        `endif
    `endif
    `ifdef DDR4_X4
        `ifdef ECC
            // Bidirectional connections
            assign DQ = {u17_r0.DQ,u16_r0.DQ,u15_r0.DQ,u14_r0.DQ,u13_r0.DQ,u12_r0.DQ,u11_r0.DQ,u10_r0.DQ,u9_r0.DQ,
                         u8_r0.DQ,u7_r0.DQ,u6_r0.DQ,u5_r0.DQ,u4_r0.DQ,u3_r0.DQ,u2_r0.DQ,u1_r0.DQ,u0_r0.DQ};
            assign DQS_t = {u17_r0.DQS_t,u16_r0.DQS_t,u15_r0.DQS_t,u14_r0.DQS_t,u13_r0.DQS_t,u12_r0.DQS_t,u11_r0.DQS_t,u10_r0.DQS_t,u9_r0.DQS_t,
                            u8_r0.DQS_t,u7_r0.DQS_t,u6_r0.DQS_t,u5_r0.DQS_t,u4_r0.DQS_t,u3_r0.DQS_t,u2_r0.DQS_t,u1_r0.DQS_t,u0_r0.DQS_t};
            assign DQS_c = {u17_r0.DQS_c,u16_r0.DQS_c,u15_r0.DQS_c,u14_r0.DQS_c,u13_r0.DQS_c,u12_r0.DQS_c,u11_r0.DQS_c,u10_r0.DQS_c,u9_r0.DQS_c,
                            u8_r0.DQS_c,u7_r0.DQS_c,u6_r0.DQS_c,u5_r0.DQS_c,u4_r0.DQS_c,u3_r0.DQS_c,u2_r0.DQS_c,u1_r0.DQS_c,u0_r0.DQS_c};
            // Controller inputs
            always @(u9_r0.ALERT_n | u10_r0.ALERT_n | u11_r0.ALERT_n | u12_r0.ALERT_n | u13_r0.ALERT_n | u14_r0.ALERT_n | u15_r0.ALERT_n | u16_r0.ALERT_n | u17_r0.ALERT_n |
                     u0_r0.ALERT_n | u1_r0.ALERT_n | u2_r0.ALERT_n | u3_r0.ALERT_n | u4_r0.ALERT_n | u5_r0.ALERT_n | u6_r0.ALERT_n | u7_r0.ALERT_n | u8_r0.ALERT_n) begin
                ALERT_n = u9_r0.ALERT_n & u10_r0.ALERT_n & u11_r0.ALERT_n & u12_r0.ALERT_n & u13_r0.ALERT_n & u14_r0.ALERT_n & u15_r0.ALERT_n & u16_r0.ALERT_n & u17_r0.ALERT_n &
                          u0_r0.ALERT_n & u1_r0.ALERT_n & u2_r0.ALERT_n & u3_r0.ALERT_n & u4_r0.ALERT_n & u5_r0.ALERT_n & u6_r0.ALERT_n & u7_r0.ALERT_n & u8_r0.ALERT_n;
            end
        `else
            // Bidirectional connections
            assign DQ = {u16_r0.DQ,u15_r0.DQ,u14_r0.DQ,u13_r0.DQ,u12_r0.DQ,u11_r0.DQ,u10_r0.DQ,u9_r0.DQ,
                         u7_r0.DQ,u6_r0.DQ,u5_r0.DQ,u4_r0.DQ,u3_r0.DQ,u2_r0.DQ,u1_r0.DQ,u0_r0.DQ};
            assign DQS_t = {u16_r0.DQS_t,u15_r0.DQS_t,u14_r0.DQS_t,u13_r0.DQS_t,u12_r0.DQS_t,u11_r0.DQS_t,u10_r0.DQS_t,u9_r0.DQS_t,
                            u7_r0.DQS_t,u6_r0.DQS_t,u5_r0.DQS_t,u4_r0.DQS_t,u3_r0.DQS_t,u2_r0.DQS_t,u1_r0.DQS_t,u0_r0.DQS_t};
            assign DQS_c = {u16_r0.DQS_c,u15_r0.DQS_c,u14_r0.DQS_c,u13_r0.DQS_c,u12_r0.DQS_c,u11_r0.DQS_c,u10_r0.DQS_c,u9_r0.DQS_c,
                            u7_r0.DQS_c,u6_r0.DQS_c,u5_r0.DQS_c,u4_r0.DQS_c,u3_r0.DQS_c,u2_r0.DQS_c,u1_r0.DQS_c,u0_r0.DQS_c};
            // Controller inputs
            always @(u9_r0.ALERT_n | u10_r0.ALERT_n | u11_r0.ALERT_n | u12_r0.ALERT_n | u13_r0.ALERT_n | u14_r0.ALERT_n | u15_r0.ALERT_n | u16_r0.ALERT_n |
                     u0_r0.ALERT_n | u1_r0.ALERT_n | u2_r0.ALERT_n | u3_r0.ALERT_n | u4_r0.ALERT_n | u5_r0.ALERT_n | u6_r0.ALERT_n | u7_r0.ALERT_n) begin
                ALERT_n = u9_r0.ALERT_n & u10_r0.ALERT_n & u11_r0.ALERT_n & u12_r0.ALERT_n & u13_r0.ALERT_n & u14_r0.ALERT_n & u15_r0.ALERT_n & u16_r0.ALERT_n &
                          u0_r0.ALERT_n & u1_r0.ALERT_n & u2_r0.ALERT_n & u3_r0.ALERT_n & u4_r0.ALERT_n & u5_r0.ALERT_n & u6_r0.ALERT_n & u7_r0.ALERT_n;
            end
        `endif
    `endif
    `ifdef DUAL_RANK
        `ifdef DDR4_X8
            `ifdef ECC
                // Bidirectional connections
                assign DQ = {u26_r1.DQ,u25_r1.DQ,u24_r1.DQ,u23_r1.DQ,u22_r1.DQ,u21_r1.DQ,u20_r1.DQ,u19_r1.DQ,u18_r1.DQ};
                assign DM_n = {u26_r1.DM_n,u25_r1.DM_n,u24_r1.DM_n,u23_r1.DM_n,u22_r1.DM_n,u21_r1.DM_n,u20_r1.DM_n,u19_r1.DM_n,u18_r1.DM_n};
                assign DQS_t = {u26_r1.DQS_t,u25_r1.DQS_t,u24_r1.DQS_t,u23_r1.DQS_t,u22_r1.DQS_t,u21_r1.DQS_t,u20_r1.DQS_t,u19_r1.DQS_t,u18_r1.DQS_t};
                assign DQS_c = {u26_r1.DQS_c,u25_r1.DQS_c,u24_r1.DQS_c,u23_r1.DQS_c,u22_r1.DQS_c,u21_r1.DQS_c,u20_r1.DQS_c,u19_r1.DQS_c,u18_r1.DQS_c};
                // Controller inputs
                always @(u18_r1.ALERT_n | u19_r1.ALERT_n | u20_r1.ALERT_n | u21_r1.ALERT_n | u22_r1.ALERT_n | u23_r1.ALERT_n | u24_r1.ALERT_n | u25_r1.ALERT_n | u26_r1.ALERT_n) begin
                    ALERT_n = u18_r1.ALERT_n & u19_r1.ALERT_n & u20_r1.ALERT_n & u21_r1.ALERT_n & u22_r1.ALERT_n & u23_r1.ALERT_n & u24_r1.ALERT_n & u25_r1.ALERT_n & u26_r1.ALERT_n;
                end
            `else
                // Bidirectional connections
                assign DQ = {u25_r1.DQ,u24_r1.DQ,u23_r1.DQ,u22_r1.DQ,u21_r1.DQ,u20_r1.DQ,u19_r1.DQ,u18_r1.DQ};
                assign DM_n = {u25_r1.DM_n,u24_r1.DM_n,u23_r1.DM_n,u22_r1.DM_n,u21_r1.DM_n,u20_r1.DM_n,u19_r1.DM_n,u18_r1.DM_n};
                assign DQS_t = {u25_r1.DQS_t,u24_r1.DQS_t,u23_r1.DQS_t,u22_r1.DQS_t,u21_r1.DQS_t,u20_r1.DQS_t,u19_r1.DQS_t,u18_r1.DQS_t};
                assign DQS_c = {u25_r1.DQS_c,u24_r1.DQS_c,u23_r1.DQS_c,u22_r1.DQS_c,u21_r1.DQS_c,u20_r1.DQS_c,u19_r1.DQS_c,u18_r1.DQS_c};
                // Controller inputs
                always @(u18_r1.ALERT_n | u19_r1.ALERT_n | u20_r1.ALERT_n | u21_r1.ALERT_n | u22_r1.ALERT_n | u23_r1.ALERT_n | u24_r1.ALERT_n | u25_r1.ALERT_n) begin
                    ALERT_n = u18_r1.ALERT_n & u19_r1.ALERT_n & u20_r1.ALERT_n & u21_r1.ALERT_n & u22_r1.ALERT_n & u23_r1.ALERT_n & u24_r1.ALERT_n & u25_r1.ALERT_n;
                end
            `endif
        `endif
        `ifdef DDR4_X4
            `ifdef ECC
                // Bidirectional connections
                assign DQ = {u35_r1.DQ,u34_r1.DQ,u33_r1.DQ,u32_r1.DQ,u31_r1.DQ,u30_r1.DQ,u29_r1.DQ,u28_r1.DQ,u27_r1.DQ,
                            u26_r1.DQ,u25_r1.DQ,u24_r1.DQ,u23_r1.DQ,u22_r1.DQ,u21_r1.DQ,u20_r1.DQ,u19_r1.DQ,u18_r1.DQ};
                assign DQS_t = {u35_r1.DQS_t,u34_r1.DQS_t,u33_r1.DQS_t,u32_r1.DQS_t,u31_r1.DQS_t,u30_r1.DQS_t,u29_r1.DQS_t,u28_r1.DQS_t,u27_r1.DQS_t,
                                u26_r1.DQS_t,u25_r1.DQS_t,u24_r1.DQS_t,u23_r1.DQS_t,u22_r1.DQS_t,u21_r1.DQS_t,u20_r1.DQS_t,u19_r1.DQS_t,u18_r1.DQS_t};
                assign DQS_c = {u35_r1.DQS_c,u34_r1.DQS_c,u33_r1.DQS_c,u32_r1.DQS_c,u31_r1.DQS_c,u30_r1.DQS_c,u29_r1.DQS_c,u28_r1.DQS_c,u27_r1.DQS_c,
                                u26_r1.DQS_c,u25_r1.DQS_c,u24_r1.DQS_c,u23_r1.DQS_c,u22_r1.DQS_c,u21_r1.DQS_c,u20_r1.DQS_c,u19_r1.DQS_c,u18_r1.DQS_c};
                // Controller inputs
                always @(u27_r1.ALERT_n | u28_r1.ALERT_n | u29_r1.ALERT_n | u30_r1.ALERT_n | u31_r1.ALERT_n | u32_r1.ALERT_n | u33_r1.ALERT_n | u34_r1.ALERT_n | u35_r1.ALERT_n |
                        u18_r1.ALERT_n | u19_r1.ALERT_n | u20_r1.ALERT_n | u21_r1.ALERT_n | u22_r1.ALERT_n | u23_r1.ALERT_n | u24_r1.ALERT_n | u25_r1.ALERT_n | u26_r1.ALERT_n) begin
                    ALERT_n = u27_r1.ALERT_n & u28_r1.ALERT_n & u29_r1.ALERT_n & u30_r1.ALERT_n & u31_r1.ALERT_n & u32_r1.ALERT_n & u33_r1.ALERT_n & u34_r1.ALERT_n & u35_r1.ALERT_n &
                            u18_r1.ALERT_n & u19_r1.ALERT_n & u20_r1.ALERT_n & u21_r1.ALERT_n & u22_r1.ALERT_n & u23_r1.ALERT_n & u24_r1.ALERT_n & u25_r1.ALERT_n & u26_r1.ALERT_n;
                end
            `else
                // Bidirectional connections
                assign DQ = {u34_r1.DQ,u33_r1.DQ,u32_r1.DQ,u31_r1.DQ,u30_r1.DQ,u29_r1.DQ,u28_r1.DQ,u27_r1.DQ,
                            u25_r1.DQ,u24_r1.DQ,u23_r1.DQ,u22_r1.DQ,u21_r1.DQ,u20_r1.DQ,u19_r1.DQ,u18_r1.DQ};
                assign DQS_t = {u34_r1.DQS_t,u33_r1.DQS_t,u32_r1.DQS_t,u31_r1.DQS_t,u30_r1.DQS_t,u29_r1.DQS_t,u28_r1.DQS_t,u27_r1.DQS_t,
                                u25_r1.DQS_t,u24_r1.DQS_t,u23_r1.DQS_t,u22_r1.DQS_t,u21_r1.DQS_t,u20_r1.DQS_t,u19_r1.DQS_t,u18_r1.DQS_t};
                assign DQS_c = {u34_r1.DQS_c,u33_r1.DQS_c,u32_r1.DQS_c,u31_r1.DQS_c,u30_r1.DQS_c,u29_r1.DQS_c,u28_r1.DQS_c,u27_r1.DQS_c,
                                u25_r1.DQS_c,u24_r1.DQS_c,u23_r1.DQS_c,u22_r1.DQS_c,u21_r1.DQS_c,u20_r1.DQS_c,u19_r1.DQS_c,u18_r1.DQS_c};
                // Controller inputs
                always @(u27_r1.ALERT_n | u28_r1.ALERT_n | u29_r1.ALERT_n | u30_r1.ALERT_n | u31_r1.ALERT_n | u32_r1.ALERT_n | u33_r1.ALERT_n | u34_r1.ALERT_n |
                        u18_r1.ALERT_n | u19_r1.ALERT_n | u20_r1.ALERT_n | u21_r1.ALERT_n | u22_r1.ALERT_n | u23_r1.ALERT_n | u24_r1.ALERT_n | u25_r1.ALERT_n) begin
                    ALERT_n = u27_r1.ALERT_n & u28_r1.ALERT_n & u29_r1.ALERT_n & u30_r1.ALERT_n & u31_r1.ALERT_n & u32_r1.ALERT_n & u33_r1.ALERT_n & u34_r1.ALERT_n &
                            u18_r1.ALERT_n & u19_r1.ALERT_n & u20_r1.ALERT_n & u21_r1.ALERT_n & u22_r1.ALERT_n & u23_r1.ALERT_n & u24_r1.ALERT_n & u25_r1.ALERT_n;
                end
            `endif
        `endif
    `endif
endinterface
