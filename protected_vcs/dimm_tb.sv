// MICRON TECHNOLOGY, INC. - CONFIDENTIAL AND PROPRIETARY INFORMATION
// /****************************************************************************************
// *
// *    File Name:  tb.sv
// *
// * Dependencies:
// *
// *  Description:  Micron SDRAM DDR4 (Double Data Rate 4) test bench
// *
// *         Note: -Set simulator resolution to "ps" accuracy
// *               -Set Debug = 0 to disable $display messages
// *
// *   Disclaimer   This software code and all associated documentation, comments or other
// *  of Warranty:  information (collectively "Software") is provided "AS IS" without
// *                warranty of any kind. MICRON TECHNOLOGY, INC. ("MTI") EXPRESSLY
// *                DISCLAIMS ALL WARRANTIES EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// *                TO, NONINFRINGEMENT OF THIRD PARTY RIGHTS, AND ANY IMPLIED WARRANTIES
// *                OF MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. MTI DOES NOT
// *                WARRANT THAT THE SOFTWARE WILL MEET YOUR REQUIREMENTS, OR THAT THE
// *                OPERATION OF THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE.
// *                FURTHERMORE, MTI DOES NOT MAKE ANY REPRESENTATIONS REGARDING THE USE OR
// *                THE RESULTS OF THE USE OF THE SOFTWARE IN TERMS OF ITS CORRECTNESS,
// *                ACCURACY, RELIABILITY, OR OTHERWISE. THE ENTIRE RISK ARISING OUT OF USE
// *                OR PERFORMANCE OF THE SOFTWARE REMAINS WITH YOU. IN NO EVENT SHALL MTI,
// *                ITS AFFILIATED COMPANIES OR THEIR SUPPLIERS BE LIABLE FOR ANY DIRECT,
// *                INDIRECT, CONSEQUENTIAL, INCIDENTAL, OR SPECIAL DAMAGES (INCLUDING,
// *                WITHOUT LIMITATION, DAMAGES FOR LOSS OF PROFITS, BUSINESS INTERRUPTION,
// *                OR LOSS OF INFORMATION) ARISING OUT OF YOUR USE OF OR INABILITY TO USE
// *                THE SOFTWARE, EVEN IF MTI HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH
// *                DAMAGES. Because some jurisdictions prohibit the exclusion or
// *                limitation of liability for consequential or incidental damages, the
// *                above limitation may not apply to you.
// *
// *                Copyright 2003 Micron Technology, Inc. All rights reserved.
// *
// ****************************************************************************************/

`timescale 1ps / 1ps

`include "arch_defines.v"
`include "StateTable.svp"
`include "dimm.vh"
module tb;
    timeunit 1ps;
    timeprecision 1ps;
    import arch_package::*;
    import proj_package::*;
    StateTable _state();
    ddr4_module_if idimm();
    reg clk_val, clk_enb;
    bit[159:0] func_str;
    UTYPE_dutconfig _dut_config;
    DDR4_cmd active_cmd;
    UTYPE_TimingParameters timing;
    wire model_enable;
    reg model_enable_val;
    wire odt_wire;
    UTYPE_cmdtype driving_cmd;

    // DQ transmit
    reg dq_en;
    reg dqs_en;
    reg[MAX_DIMM_DQ_BITS-1:0] dq_out;
    reg[MAX_DIMM_DQS_BITS-1:0] dqs_out;
    reg[MAX_DIMM_DM_BITS-1:0] dm_out;
    `ifdef DDR4_X4
        parameter int CONFIGURED_DQ_BITS = 4;
        parameter int CONFIGURED_RANKS = 1;
    `endif
    `ifdef DDR4_X8
        parameter int CONFIGURED_DQ_BITS = 8;
        parameter int CONFIGURED_RANKS = 1;
    `endif
    `ifdef DDR4_X16
        parameter int CONFIGURED_DQ_BITS = 16;
        parameter int CONFIGURED_RANKS = 1;
    `endif
    `ifdef DDR4_2G
        parameter UTYPE_density CONFIGURED_DENSITY = _2G;
    `elsif DDR4_4G
        parameter UTYPE_density CONFIGURED_DENSITY = _4G;
    `elsif DDR4_8G
        parameter UTYPE_density CONFIGURED_DENSITY = _8G;
    `elsif DDR4_16G
        parameter UTYPE_density CONFIGURED_DENSITY = _16G;
    `endif
    `include "timing_tasks.sv"

     // dummy interface, _state needs access to iDDR4.CK[1]
     DDR4_if #(.CONFIGURED_DQ_BITS(8)) iDDR4();
     assign iDDR4.CK[1] = idimm.CK[1];

    `ifdef DDR4_X8
        `ifdef ECC
            assign {idimm.u8_r0.DQ,idimm.u7_r0.DQ,idimm.u6_r0.DQ,idimm.u5_r0.DQ,idimm.u4_r0.DQ,idimm.u3_r0.DQ,idimm.u2_r0.DQ,idimm.u1_r0.DQ,idimm.u0_r0.DQ} =
                    dq_en ? {dq_out[71:64],dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
            assign {idimm.u8_r0.DM_n,idimm.u7_r0.DM_n,idimm.u6_r0.DM_n,idimm.u5_r0.DM_n,idimm.u4_r0.DM_n,idimm.u3_r0.DM_n,idimm.u2_r0.DM_n,idimm.u1_r0.DM_n,idimm.u0_r0.DM_n} =
                    dq_en ? {dm_out[8],dm_out[7],dm_out[6],dm_out[5],dm_out[4],dm_out[3],dm_out[2],dm_out[1],dm_out[0]} : {MAX_DIMM_DM_BITS{1'bz}};
            assign {idimm.u8_r0.DQS_t,idimm.u7_r0.DQS_t,idimm.u6_r0.DQS_t,idimm.u5_r0.DQS_t,idimm.u4_r0.DQS_t,idimm.u3_r0.DQS_t,idimm.u2_r0.DQS_t,idimm.u1_r0.DQS_t,idimm.u0_r0.DQS_t} =
                    dqs_en ? {dqs_out[8],dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            assign {idimm.u8_r0.DQS_c,idimm.u7_r0.DQS_c,idimm.u6_r0.DQS_c,idimm.u5_r0.DQS_c,idimm.u4_r0.DQS_c,idimm.u3_r0.DQS_c,idimm.u2_r0.DQS_c,idimm.u1_r0.DQS_c,idimm.u0_r0.DQS_c} =
                    dqs_en ? {~dqs_out[8],~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
        `else
            assign {idimm.u7_r0.DQ,idimm.u6_r0.DQ,idimm.u5_r0.DQ,idimm.u4_r0.DQ,idimm.u3_r0.DQ,idimm.u2_r0.DQ,idimm.u1_r0.DQ,idimm.u0_r0.DQ} =
                    dq_en ? {dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
            assign {idimm.u7_r0.DM_n,idimm.u6_r0.DM_n,idimm.u5_r0.DM_n,idimm.u4_r0.DM_n,idimm.u3_r0.DM_n,idimm.u2_r0.DM_n,idimm.u1_r0.DM_n,idimm.u0_r0.DM_n} =
                    dq_en ? {dm_out[7],dm_out[6],dm_out[5],dm_out[4],dm_out[3],dm_out[2],dm_out[1],dm_out[0]} : {MAX_DIMM_DM_BITS{1'bz}};
            assign {idimm.u7_r0.DQS_t,idimm.u6_r0.DQS_t,idimm.u5_r0.DQS_t,idimm.u4_r0.DQS_t,idimm.u3_r0.DQS_t,idimm.u2_r0.DQS_t,idimm.u1_r0.DQS_t,idimm.u0_r0.DQS_t} =
                    dqs_en ? {dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            assign {idimm.u7_r0.DQS_c,idimm.u6_r0.DQS_c,idimm.u5_r0.DQS_c,idimm.u4_r0.DQS_c,idimm.u3_r0.DQS_c,idimm.u2_r0.DQS_c,idimm.u1_r0.DQS_c,idimm.u0_r0.DQS_c} =
                    dqs_en ? {~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
        `endif
    `endif
    `ifdef DDR4_X4
        `ifdef ECC
            assign {idimm.u17_r0.DQ,idimm.u16_r0.DQ,idimm.u15_r0.DQ,idimm.u14_r0.DQ,idimm.u13_r0.DQ,idimm.u12_r0.DQ,idimm.u11_r0.DQ,idimm.u10_r0.DQ,idimm.u9_r0.DQ,
                         idimm.u8_r0.DQ,idimm.u7_r0.DQ,idimm.u6_r0.DQ,idimm.u5_r0.DQ,idimm.u4_r0.DQ,idimm.u3_r0.DQ,idimm.u2_r0.DQ,idimm.u1_r0.DQ,idimm.u0_r0.DQ} =
                        dq_en ? {dq_out[71:64],dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
            assign {idimm.u17_r0.DQS_t,idimm.u16_r0.DQS_t,idimm.u15_r0.DQS_t,idimm.u14_r0.DQS_t,idimm.u13_r0.DQS_t,idimm.u12_r0.DQS_t,idimm.u11_r0.DQS_t,idimm.u10_r0.DQS_t,idimm.u9_r0.DQS_t,
                            idimm.u8_r0.DQS_t,idimm.u7_r0.DQS_t,idimm.u6_r0.DQS_t,idimm.u5_r0.DQS_t,idimm.u4_r0.DQS_t,idimm.u3_r0.DQS_t,idimm.u2_r0.DQS_t,idimm.u1_r0.DQS_t,idimm.u0_r0.DQS_t} =
                            dqs_en ? {dqs_out[8],dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0],dqs_out[8],dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            assign {idimm.u17_r0.DQS_c,idimm.u16_r0.DQS_c,idimm.u15_r0.DQS_c,idimm.u14_r0.DQS_c,idimm.u13_r0.DQS_c,idimm.u12_r0.DQS_c,idimm.u11_r0.DQS_c,idimm.u10_r0.DQS_c,idimm.u9_r0.DQS_c,
                            idimm.u8_r0.DQS_c,idimm.u7_r0.DQS_c,idimm.u6_r0.DQS_c,idimm.u5_r0.DQS_c,idimm.u4_r0.DQS_c,idimm.u3_r0.DQS_c,idimm.u2_r0.DQS_c,idimm.u1_r0.DQS_c,idimm.u0_r0.DQS_c} =
                            dqs_en ? {~dqs_out[8],~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0],~dqs_out[8],~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
        `else
            assign {idimm.u16_r0.DQ,idimm.u15_r0.DQ,idimm.u14_r0.DQ,idimm.u13_r0.DQ,idimm.u12_r0.DQ,idimm.u11_r0.DQ,idimm.u10_r0.DQ,idimm.u9_r0.DQ,
                         idimm.u7_r0.DQ,idimm.u6_r0.DQ,idimm.u5_r0.DQ,idimm.u4_r0.DQ,idimm.u3_r0.DQ,idimm.u2_r0.DQ,idimm.u1_r0.DQ,idimm.u0_r0.DQ} =
                         dq_en ? {dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
            assign {idimm.u16_r0.DQS_t,idimm.u15_r0.DQS_t,idimm.u14_r0.DQS_t,idimm.u13_r0.DQS_t,idimm.u12_r0.DQS_t,idimm.u11_r0.DQS_t,idimm.u10_r0.DQS_t,idimm.u9_r0.DQS_t,
                            idimm.u7_r0.DQS_t,idimm.u6_r0.DQS_t,idimm.u5_r0.DQS_t,idimm.u4_r0.DQS_t,idimm.u3_r0.DQS_t,idimm.u2_r0.DQS_t,idimm.u1_r0.DQS_t,idimm.u0_r0.DQS_t} =
                            dqs_en ? {dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            assign {idimm.u16_r0.DQS_c,idimm.u15_r0.DQS_c,idimm.u14_r0.DQS_c,idimm.u13_r0.DQS_c,idimm.u12_r0.DQS_c,idimm.u11_r0.DQS_c,idimm.u10_r0.DQS_c,idimm.u9_r0.DQS_c,
                            idimm.u7_r0.DQS_c,idimm.u6_r0.DQS_c,idimm.u5_r0.DQS_c,idimm.u4_r0.DQS_c,idimm.u3_r0.DQS_c,idimm.u2_r0.DQS_c,idimm.u1_r0.DQS_c,idimm.u0_r0.DQS_c} =
                            dqs_en ? {~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
        `endif
    `endif
    `ifdef DUAL_RANK
        `ifdef DDR4_X8
            `ifdef ECC
                assign {idimm.u26_r1.DQ,idimm.u25_r1.DQ,idimm.u24_r1.DQ,idimm.u23_r1.DQ,idimm.u22_r1.DQ,idimm.u21_r1.DQ,idimm.u20_r1.DQ,idimm.u19_r1.DQ,idimm.u18_r1.DQ} =
                        dq_en ? {dq_out[71:64],dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
                assign {idimm.u26_r1.DM_n,idimm.u25_r1.DM_n,idimm.u24_r1.DM_n,idimm.u23_r1.DM_n,idimm.u22_r1.DM_n,idimm.u21_r1.DM_n,idimm.u20_r1.DM_n,idimm.u19_r1.DM_n,idimm.u18_r1.DM_n} =
                        dq_en ? {dm_out[8],dm_out[7],dm_out[6],dm_out[5],dm_out[4],dm_out[3],dm_out[2],dm_out[1],dm_out[0]} : {MAX_DIMM_DM_BITS{1'bz}};
                assign {idimm.u26_r1.DQS_t,idimm.u25_r1.DQS_t,idimm.u24_r1.DQS_t,idimm.u23_r1.DQS_t,idimm.u22_r1.DQS_t,idimm.u21_r1.DQS_t,idimm.u20_r1.DQS_t,idimm.u19_r1.DQS_t,idimm.u18_r1.DQS_t} =
                        dqs_en ? {dqs_out[8],dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
                assign {idimm.u26_r1.DQS_c,idimm.u25_r1.DQS_c,idimm.u24_r1.DQS_c,idimm.u23_r1.DQS_c,idimm.u22_r1.DQS_c,idimm.u21_r1.DQS_c,idimm.u20_r1.DQS_c,idimm.u19_r1.DQS_c,idimm.u18_r1.DQS_c} =
                        dqs_en ? {~dqs_out[8],~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            `else
                assign {idimm.u25_r1.DQ,idimm.u24_r1.DQ,idimm.u23_r1.DQ,idimm.u22_r1.DQ,idimm.u21_r1.DQ,idimm.u20_r1.DQ,idimm.u19_r1.DQ,idimm.u18_r1.DQ} =
                        dq_en ? {dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
                assign {idimm.u25_r1.DM_n,idimm.u24_r1.DM_n,idimm.u23_r1.DM_n,idimm.u22_r1.DM_n,idimm.u21_r1.DM_n,idimm.u20_r1.DM_n,idimm.u19_r1.DM_n,idimm.u18_r1.DM_n} =
                        dq_en ? {dm_out[7],dm_out[6],dm_out[5],dm_out[4],dm_out[3],dm_out[2],dm_out[1],dm_out[0]} : {MAX_DIMM_DM_BITS{1'bz}};
                assign {idimm.u25_r1.DQS_t,idimm.u24_r1.DQS_t,idimm.u23_r1.DQS_t,idimm.u22_r1.DQS_t,idimm.u21_r1.DQS_t,idimm.u20_r1.DQS_t,idimm.u19_r1.DQS_t,idimm.u18_r1.DQS_t} =
                        dqs_en ? {dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
                assign {idimm.u25_r1.DQS_c,idimm.u24_r1.DQS_c,idimm.u23_r1.DQS_c,idimm.u22_r1.DQS_c,idimm.u21_r1.DQS_c,idimm.u20_r1.DQS_c,idimm.u19_r1.DQS_c,idimm.u18_r1.DQS_c} =
                        dqs_en ? {~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            `endif
        `endif
        `ifdef DDR4_X4
            `ifdef ECC
                assign {idimm.u35_r1.DQ,idimm.u34_r1.DQ,idimm.u33_r1.DQ,idimm.u32_r1.DQ,idimm.u31_r1.DQ,idimm.u30_r1.DQ,idimm.u29_r1.DQ,idimm.u28_r1.DQ,idimm.u27_r1.DQ,
                            idimm.u26_r1.DQ,idimm.u25_r1.DQ,idimm.u24_r1.DQ,idimm.u23_r1.DQ,idimm.u22_r1.DQ,idimm.u21_r1.DQ,idimm.u20_r1.DQ,idimm.u19_r1.DQ,idimm.u18_r1.DQ} =
                            dq_en ? {dq_out[71:64],dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
                assign {idimm.u35_r1.DQS_t,idimm.u34_r1.DQS_t,idimm.u33_r1.DQS_t,idimm.u32_r1.DQS_t,idimm.u31_r1.DQS_t,idimm.u30_r1.DQS_t,idimm.u29_r1.DQS_t,idimm.u28_r1.DQS_t,idimm.u27_r1.DQS_t,
                                idimm.u26_r1.DQS_t,idimm.u25_r1.DQS_t,idimm.u24_r1.DQS_t,idimm.u23_r1.DQS_t,idimm.u22_r1.DQS_t,idimm.u21_r1.DQS_t,idimm.u20_r1.DQS_t,idimm.u19_r1.DQS_t,idimm.u18_r1.DQS_t} =
                                dqs_en ? {dqs_out[8],dqs_out[7],dqs_out[6],dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0],dqs_out[8],dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
                assign {idimm.u35_r1.DQS_c,idimm.u34_r1.DQS_c,idimm.u33_r1.DQS_c,idimm.u32_r1.DQS_c,idimm.u31_r1.DQS_c,idimm.u30_r1.DQS_c,idimm.u29_r1.DQS_c,idimm.u28_r1.DQS_c,idimm.u27_r1.DQS_c,
                                idimm.u26_r1.DQS_c,idimm.u25_r1.DQS_c,idimm.u24_r1.DQS_c,idimm.u23_r1.DQS_c,idimm.u22_r1.DQS_c,idimm.u21_r1.DQS_c,idimm.u20_r1.DQS_c,idimm.u19_r1.DQS_c,idimm.u18_r1.DQS_c} =
                                dqs_en ? {~dqs_out[8],~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0],~dqs_out[8],~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            `else
                assign {idimm.u34_r1.DQ,idimm.u33_r1.DQ,idimm.u32_r1.DQ,idimm.u31_r1.DQ,idimm.u30_r1.DQ,idimm.u29_r1.DQ,idimm.u28_r1.DQ,idimm.u27_r1.DQ,
                            idimm.u25_r1.DQ,idimm.u24_r1.DQ,idimm.u23_r1.DQ,idimm.u22_r1.DQ,idimm.u21_r1.DQ,idimm.u20_r1.DQ,idimm.u19_r1.DQ,idimm.u18_r1.DQ} =
                            dq_en ? {dq_out[63:56],dq_out[55:48],dq_out[47:40],dq_out[39:32],dq_out[31:24],dq_out[23:16],dq_out[15:8],dq_out[7:0]} : {MAX_DIMM_DQ_BITS{1'bz}};
                assign {idimm.u34_r1.DQS_t,idimm.u33_r1.DQS_t,idimm.u32_r1.DQS_t,idimm.u31_r1.DQS_t,idimm.u30_r1.DQS_t,idimm.u29_r1.DQS_t,idimm.u28_r1.DQS_t,idimm.u27_r1.DQS_t,
                                idimm.u25_r1.DQS_t,idimm.u24_r1.DQS_t,idimm.u23_r1.DQS_t,idimm.u22_r1.DQS_t,idimm.u21_r1.DQS_t,idimm.u20_r1.DQS_t,idimm.u19_r1.DQS_t,idimm.u18_r1.DQS_t} =
                                dqs_en ? {dqs_out[7],dqs_out[6],dqs_out[5],dqs_out[4],dqs_out[3],dqs_out[2],dqs_out[1],dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
                assign {idimm.u34_r1.DQS_c,idimm.u33_r1.DQS_c,idimm.u32_r1.DQS_c,idimm.u31_r1.DQS_c,idimm.u30_r1.DQS_c,idimm.u29_r1.DQS_c,idimm.u28_r1.DQS_c,idimm.u27_r1.DQS_c,
                                idimm.u25_r1.DQS_c,idimm.u24_r1.DQS_c,idimm.u23_r1.DQS_c,idimm.u22_r1.DQS_c,idimm.u21_r1.DQS_c,idimm.u20_r1.DQS_c,idimm.u19_r1.DQS_c,idimm.u18_r1.DQS_c} =
                                dqs_en ? {~dqs_out[7],~dqs_out[6],~dqs_out[5],~dqs_out[4],~dqs_out[3],~dqs_out[2],~dqs_out[1],~dqs_out[0]} : {MAX_DIMM_DQS_BITS{1'bz}};
            `endif
        `endif
    `endif

    assign model_enable = model_enable_val;

    // DQ receive
    reg[MAX_DIMM_DM_BITS-1:0] dm_fifo [4*(MAX_RL+MAX_BURST_LEN+MAX_CAL):0];
    reg[MAX_DIMM_DQ_BITS-1:0] dq_fifo [4*(MAX_RL+MAX_BURST_LEN+MAX_CAL):0];
    wire[MAX_DIMM_DQ_BITS-1:0] q0, q1, q2, q3;
    reg ptr_rst_n;
    reg[1:0] burst_cntr;

    reg odt_out;
    reg[MAX_RL:0] odt_fifo;
//     assign idimm.ODT = odt_out & !odt_fifo[0];

    initial begin
        $timeformat (-9, 1, " ns", 1);
        _dut_config.by_mode = CONFIGURED_DQ_BITS;
        _dut_config.density = CONFIGURED_DENSITY;
        _dut_config.ranks = CONFIGURED_RANKS;
        arch_package::dut_config_populate(_dut_config);
        proj_package::project_dut_config(_dut_config);
        _state.Initialize("tb", _dut_config, 0);
        active_cmd = new();
        idimm.CK <= 2'b01;
        clk_enb <= 1'b1;
        clk_val <= 1'b1;
        odt_fifo <= 0;
        model_enable_val = 1;
    end

    always @(active_cmd.cmd) begin
        driving_cmd = active_cmd.cmd;
    end
    // Component instantiation
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u0_r0(.model_enable(model_enable), .iDDR4(idimm.u0_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u1_r0(.model_enable(model_enable), .iDDR4(idimm.u1_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u2_r0(.model_enable(model_enable), .iDDR4(idimm.u2_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u3_r0(.model_enable(model_enable), .iDDR4(idimm.u3_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u4_r0(.model_enable(model_enable), .iDDR4(idimm.u4_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u5_r0(.model_enable(model_enable), .iDDR4(idimm.u5_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u6_r0(.model_enable(model_enable), .iDDR4(idimm.u6_r0));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u7_r0(.model_enable(model_enable), .iDDR4(idimm.u7_r0));
    `ifdef ECC
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u8_r0(.model_enable(model_enable), .iDDR4(idimm.u8_r0));
    `endif
    `ifdef DDR4_X4
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u9_r0(.model_enable(model_enable), .iDDR4(idimm.u9_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u10_r0(.model_enable(model_enable), .iDDR4(idimm.u10_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u11_r0(.model_enable(model_enable), .iDDR4(idimm.u11_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u12_r0(.model_enable(model_enable), .iDDR4(idimm.u12_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u13_r0(.model_enable(model_enable), .iDDR4(idimm.u13_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u14_r0(.model_enable(model_enable), .iDDR4(idimm.u14_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u15_r0(.model_enable(model_enable), .iDDR4(idimm.u15_r0));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u16_r0(.model_enable(model_enable), .iDDR4(idimm.u16_r0));
        `ifdef ECC
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u17_r0(.model_enable(model_enable), .iDDR4(idimm.u17_r0));
        `endif
    `endif
    `ifdef DUAL_RANK
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u18_r1(.model_enable(model_enable), .iDDR4(idimm.u18_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u19_r1(.model_enable(model_enable), .iDDR4(idimm.u19_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u20_r1(.model_enable(model_enable), .iDDR4(idimm.u20_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u21_r1(.model_enable(model_enable), .iDDR4(idimm.u21_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u22_r1(.model_enable(model_enable), .iDDR4(idimm.u22_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u23_r1(.model_enable(model_enable), .iDDR4(idimm.u23_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u24_r1(.model_enable(model_enable), .iDDR4(idimm.u24_r1));
        ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u25_r1(.model_enable(model_enable), .iDDR4(idimm.u25_r1));
        `ifdef ECC
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u26_r1(.model_enable(model_enable), .iDDR4(idimm.u26_r1));
        `endif
        `ifdef DDR4_X4
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u27_r1(.model_enable(model_enable), .iDDR4(idimm.u27_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u28_r1(.model_enable(model_enable), .iDDR4(idimm.u28_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u29_r1(.model_enable(model_enable), .iDDR4(idimm.u29_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u30_r1(.model_enable(model_enable), .iDDR4(idimm.u30_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u31_r1(.model_enable(model_enable), .iDDR4(idimm.u31_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u32_r1(.model_enable(model_enable), .iDDR4(idimm.u32_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u33_r1(.model_enable(model_enable), .iDDR4(idimm.u33_r1));
            ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u34_r1(.model_enable(model_enable), .iDDR4(idimm.u34_r1));
            `ifdef ECC
                ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS)) u35_r1(.model_enable(model_enable), .iDDR4(idimm.u35_r1));
            `endif
        `endif
    `endif
    // Clock generator
    always @(posedge clk_val && clk_enb) begin
      clk_val <= #(timing.tCK/2) 1'b0;
      clk_val <= #(timing.tCK) 1'b1;
      idimm.CK[1] <= #(timing.tCK/2) 1'b0;
      idimm.CK[1] <= #(timing.tCK) 1'b1;
      idimm.CK[0] <= #(timing.tCK/2) 1'b1;
      idimm.CK[0] <= #(timing.tCK) 1'b0;
    end

    // NCVerilog requires local references to structures.
    UTYPE_DutModeConfig _dut_mode_config;
    always @(_state.s_dut_mode_config or timing.tCK or timing.tDQSCK_dll_off or timing.tDQSCK_dll_on) begin
        _dut_mode_config = _state.s_dut_mode_config;
        timing.tRDPDENc = _dut_mode_config.RL + 4 + 1;
        if (rBL4 == _dut_mode_config.BL_reg) begin
            timing.tWRPDENc = _dut_mode_config.WL_calculated + 2 + timing.tWRc + _dut_mode_config.CAL;
            timing.tWRAPDENc = _dut_mode_config.WL_calculated + 2 + _dut_mode_config.write_recovery + 1 + _dut_mode_config.CAL;
        end else begin
            timing.tWRPDENc = _dut_mode_config.WL_calculated + 4 + timing.tWRc + _dut_mode_config.CAL;
            timing.tWRAPDENc = _dut_mode_config.WL_calculated + 4 + _dut_mode_config.write_recovery + 1 + _dut_mode_config.CAL;
        end
        timing.tCCDc_L = _dut_mode_config.tCCD_L;
        timing.tCCD_L = _dut_mode_config.tCCD_L * timing.tCK;
        timing.tRTPc = _dut_mode_config.write_recovery / 2;
        timing.tRTP = (_dut_mode_config.write_recovery / 2) * timing.tCK;
        if (0 == _dut_mode_config.DLL_enable) begin
            if (timing.tDQSCK_dll_off > timing.tCK)
                timing.tDQSCK = timing.tDQSCK_dll_off % timing.tCK;
            else
                timing.tDQSCK = timing.tDQSCK_dll_off;
            // Force RL to update if necessary.
            _state.s_dut_mode_config = _state.AddrToModeDecode(_state._LMR_cache[1][2] | MR6, _state.s_dut_mode_config);
        end else begin
            timing.tDQSCK = timing.tDQSCK_dll_on;
        end
        if (2 == _dut_mode_config.wr_preamble_clocks) begin
            timing.tDQSSp_min = timing.tDQSSp_2tCK_min;
            timing.tDQSSp_min = timing.tDQSSp_2tCK_min;
        end else begin
            timing.tDQSSp_min = timing.tDQSSp_1tCK_min;
            timing.tDQSSp_min = timing.tDQSSp_1tCK_min;
        end
        timing.tWR_CRC_DMc = _dut_mode_config.delay_write_crc_dm;
    end

    task power_up();
        func_str = "power_up";
        idimm.CS_n = '0;
        idimm.ACT_n <= 1;
        idimm.RAS_n_A16 <= 1;
        idimm.CAS_n_A15 <= 1;
        idimm.WE_n_A14 <= 1;
        idimm.CKE <= 0;
        idimm.TEN <= 0;
        idimm.PARITY <= 0;
        idimm.ALERT_n <= 1;
        idimm.RESET_n <= 0;
        idimm.ZQ <= 0;
        idimm.PWR <= 0;
        idimm.VREF_CA <= 0;
        idimm.VREF_DQ <= 0;
        #(timing.tRESET);
        idimm.PWR <= 1;
        idimm.VREF_CA <= 1;
        idimm.VREF_DQ <= 1;
        #(timing.tPWRUP);
        idimm.RESET_n <= 1;

        #(timing.tRESETCKE);
        deselect(timing.tPDc);
        odt_out <= 1'b0;
        // After CKE is registered HIGH and after tXPR has been satisfied, MRS commands may be issued.
        @(negedge clk_val) deselect(timing.tXPR/timing.tCK);
        active_cmd.cmd = cmdPDX;
        active_cmd.tCK = timing.tCK;
        _state.UpdateTable(active_cmd);
    endtask

    task precharge_power_down(int count);
        func_str = "precharge_power_down";
        idimm.CKE <= 1'b0;
        idimm.CS_n  <= '1;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdPPDE;
        active_cmd.tCK = timing.tCK;
        _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task active_power_down(int count);
        func_str = "active_power_down";
        idimm.CKE <= 1'b0;
        idimm.CS_n  <= '1;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdAPDE;
        active_cmd.tCK = timing.tCK;
        _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task load_mode(reg[MAX_BANK_GROUP_BITS-1:0] bg,
                   reg[MAX_BANK_BITS-1:0] ba,
                   reg[MODEREG_BITS-1:0] addr,
                   reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0
                   );
        func_str = "load_mode";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b0;
        idimm.CAS_n_A15 <= 1'b0;
        idimm.WE_n_A14  <= 1'b0;
        idimm.BG <= bg;
        idimm.BA <= ba;
        idimm.ADDR <= addr;
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdLMR, r, bg, ba, addr[13:0], timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, r, bg, ba, addr[13:0], timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    task refresh(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0, reg[MAX_BANK_GROUP_BITS-1:0] bg = 0, reg[MAX_BANK_BITS-1:0] ba = 0);
        func_str = "refresh";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b0;
        idimm.CAS_n_A15 <= 1'b0;
        idimm.WE_n_A14  <= 1'b1;
        idimm.BG  <= bg;
        idimm.BA  <= ba;
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdREF, r, bg, ba, idimm.ADDR, timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, r, bg, ba, idimm.ADDR, timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    task precharge(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0,
                   reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
                   reg[MAX_BANK_BITS-1:0] ba = '0,
                   bit ap = 0); // Precharge all
        func_str = "precharge";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b0;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b0;
        idimm.BG  <= bg;
        idimm.BA  <= ba;
        idimm.ADDR <= (ap<<10);
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdPRE, r, bg, ba, (ap<<AUTOPRECHARGEADDR), timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, r, bg, ba, (ap<<AUTOPRECHARGEADDR), timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    task activate(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0,
                  reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
                  reg[MAX_BANK_BITS-1:0] ba = '0,
                  reg[MAX_ROW_ADDR_BITS-1:0] row = '0);
        func_str = "activate";
        idimm.CKE <= 1'b1;
        idimm.CS_n <= rank_cs;
        idimm.ACT_n <= 1'b0;
        idimm.RAS_n_A16 <= row[16];
        idimm.CAS_n_A15 <= row[15];
        idimm.WE_n_A14 <= row[14];
        idimm.BG <= bg;
        idimm.BA <= ba;
        idimm.ADDR <= row;
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdACT, r, bg, ba, row, timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, r, bg, ba, row, timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    // Write task supports burst lengths <= 8
    task write(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0,
               reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
               reg[MAX_BANK_BITS-1:0] ba = '0,
               reg[MAX_COL_ADDR_BITS-1:0] col = '0,
               bit ap = 0, // Auto Precharge
               bit bc = 0, // Burst Chop
               reg[MAX_BURST_LEN*MAX_DIMM_DM_BITS-1:0] dm = '0,
               reg[MAX_BURST_LEN*MAX_DIMM_DQ_BITS-1:0] dq = '0
               );
        int wl, bl;
        reg[MAX_ADDR_BITS-1:0] drive_addr[2:0];

        func_str = "write";
        drive_addr[0] = col & _dut_config.col_mask; // addr[9:0] = COL[9:0]
        drive_addr[1] = ((col >> 10) & 1'h1) << 11; // addr[11] = COL[10]
        drive_addr[2] = (col >> 11) << 13;         // addr[N:13] = COL[N:11]
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b0;
        idimm.WE_n_A14  <= 1'b0;
        idimm.BG  <= bg;
        idimm.BA  <= ba;
        idimm.ADDR <= drive_addr[0] | drive_addr[1] | drive_addr[2] |
                      (ap << AUTOPRECHARGEADDR) | (bc << BLFLYSELECT);

        wl = _dut_mode_config.WL_calculated;
        bl = _state.CheckFlyBL(bc << BLFLYSELECT);
        dqs_en <= #(wl*timing.tCK-timing.tCK/2) 1'b1;
        dqs_out <= #(wl*timing.tCK-timing.tCK/2) {MAX_DIMM_DQS_BITS{1'b1}};
        for (int i=0; i<=bl; i++) begin
            dqs_en <= #(wl*timing.tCK + i*timing.tCK/2) 1'b1;
            if (i%2 == 0) begin
                dqs_out <= #(wl*timing.tCK + i*timing.tCK/2) {MAX_DIMM_DQS_BITS{1'b0}};
            end else begin
                dqs_out <= #(wl*timing.tCK + i*timing.tCK/2) {MAX_DIMM_DQS_BITS{1'b1}};
            end

            dq_en  <= #(wl*timing.tCK + i*timing.tCK/2 + timing.tCK/4) 1'b1;
            dm_out <= #(wl*timing.tCK + i*timing.tCK/2 + timing.tCK/4) dm>>i*MAX_DIMM_DM_BITS;
            dq_out <= #(wl*timing.tCK + i*timing.tCK/2 + timing.tCK/4) dq>>i*MAX_DIMM_DQ_BITS;
        end
        dqs_en <= #(wl*timing.tCK + bl*timing.tCK/2 + timing.tCK/2) 1'b0;
        dq_en  <= #(wl*timing.tCK + bl*timing.tCK/2 + timing.tCK/4) 1'b0;
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdWR, r, bg, ba, col, timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, r, bg, ba, col, timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    // Read without data verification
    task read(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0,
              reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
              reg[MAX_BANK_BITS-1:0] ba = '0,
              reg[MAX_COL_ADDR_BITS-1:0] col = '0,
              bit ap = 0, // Auto Precharge
              bit bc = 0 // Burst Chop
             );
        int wl, rl, bl;
        reg[MAX_ADDR_BITS-1:0] drive_addr[2:0];

        func_str = "read";
        drive_addr[0] = col & _dut_config.col_mask; // addr[9:0] = COL[9:0]
        drive_addr[1] = ((col >> 10) & 1'h1) << 11; // addr[11] = COL[10]
        drive_addr[2] = (col >> 11) << 13;         // addr[N:13] = COL[N:11]
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b0;
        idimm.WE_n_A14  <= 1'b1;
        idimm.BG  <= bg;
        idimm.BA  <= ba;
        idimm.ADDR <= drive_addr[0] | drive_addr[1] | drive_addr[2] |
                      (ap << AUTOPRECHARGEADDR) | (bc << BLFLYSELECT);

        wl = _dut_mode_config.WL_calculated;
        rl = _dut_mode_config.RL;
        bl = _state.CheckFlyBL(bc << BLFLYSELECT);

        for (int i=0; i<(bl/2 + 2); i=i+1) begin
            odt_fifo[rl-wl + i] = 1'b1;
        end
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdRD, r, bg, ba, col, timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, r, bg, ba, col, timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    task zq_cs(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0, reg[MAX_ADDR_BITS-1:0] addr = '0);
        func_str = "zq_cs";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b0;
        addr = addr & ~(1'b1 << AUTOPRECHARGEADDR);
        idimm.ADDR <= addr;
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdZQ, idimm.C, idimm.BG, idimm.BA, addr, timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, idimm.C, idimm.BG, idimm.BA, addr, timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    task zq_cl(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0, reg[MAX_ADDR_BITS-1:0] addr = '0);
        func_str = "zq_cs";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b0;
        addr = addr | (1'b1 << AUTOPRECHARGEADDR);
        idimm.ADDR <= addr;
        for (int r=0;r<MAX_DIMM_CS_BITS;r++) begin
            if (0 == rank_cs[r]) begin
                active_cmd.Populate(cmdZQ, idimm.C, idimm.BG, idimm.BA, addr, timing.tCK);
            end else begin
                active_cmd.Populate(cmdNOP, idimm.C, idimm.BG, idimm.BA, addr, timing.tCK);
            end
            _state.UpdateTable(active_cmd);
        end
        @(negedge clk_val);
    endtask

    task nop(int count, reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0);
        func_str = "nop";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdNOP;
        active_cmd.tCK = timing.tCK;
        repeat(count) _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task deselect(int count);
        func_str = "deselect";
        idimm.CKE <= 1'b1;
        idimm.CS_n  <= '1;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdNOP;
        active_cmd.tCK = timing.tCK;
        repeat(count) _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task deselect_cs_cke(int count, reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '1, logic cke);
        func_str = "deselect";
        idimm.CKE <= cke;
        idimm.CS_n  <= rank_cs;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdNOP;
        active_cmd.tCK = timing.tCK;
        repeat(count) _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task self_refresh(int count);
        func_str = "self_refresh";
        idimm.CKE <= 1'b0;
        idimm.CS_n  <= '0;
        idimm.ACT_n <= 1'b1;
        idimm.RAS_n_A16 <= 1'b0;
        idimm.CAS_n_A15 <= 1'b0;
        idimm.WE_n_A14  <= 1'b1;
        @(negedge clk_val);
        idimm.CS_n  <= '1;
        idimm.RAS_n_A16 <= 1'b1;
        idimm.CAS_n_A15 <= 1'b1;
        idimm.WE_n_A14  <= 1'b1;
        @(negedge clk_val);
        active_cmd.cmd = cmdSREFE;
        active_cmd.tCK = timing.tCK;
        _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task default_period(UTYPE_TS new_ts);
        SetTimingStruct(new_ts);
        timing.tCK = tCK;
        _state.UpdateTiming(timing);
        $display("%m at time %0t: INFO: Default Clock Period to %s (%0d ps)", $time, new_ts.name(), timing.tCK);
        @(negedge clk_val);
        #(timing.tPD);
    endtask

    task sr_change_period(UTYPE_TS new_ts);
        func_str = "sr_change_period";
        self_refresh(timing.tCKSREc + 1);
        deselect_cs_cke(.count(timing.tCKSREc), .rank_cs('1), .cke(0));
        SetTimingStruct(new_ts);
        timing.tCK = tCK;
        _state.UpdateTiming(timing);
        deselect_cs_cke(.count(timing.tCKSRXc), .rank_cs('1), .cke(0));
        $display("%m at time %0t: INFO: Changing Clock Period to %s (%0d ps)", $time, new_ts.name(), timing.tCK);
        deselect(.count(timing.tXSc));
        @(negedge clk_val);
    endtask

    // Read with data verification
    task read_verify(reg[MAX_DIMM_CS_BITS-1:0] rank_cs = '0,
                     reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
                     reg[MAX_BANK_BITS-1:0] ba = '0,
                     reg[MAX_COL_ADDR_BITS-1:0] col = '0,
                     bit ap = 0, // Auto Precharge
                     bit bc = 0, // Burst Chop
                     reg[MAX_BURST_LEN*MAX_DIMM_DM_BITS-1:0] dm = '0, // Expected Data Mask
                     reg[MAX_BURST_LEN*MAX_DIMM_DQ_BITS-1:0] dq = '0 // Expected Data
                    );
        int rl, bl;

        func_str = "read_verify";
        read(.rank_cs(rank_cs), .bg(bg), .ba(ba), .col(col), .ap(ap), .bc(bc));
        rl = _dut_mode_config.RL;
        bl = _state.CheckFlyBL(bc << BLFLYSELECT);
        dq = BurstOrderData(dq, col, bl, _dut_mode_config.BT);
        fork // this must take place after current clock falling edge
        begin
            #1;
            for (int i=0; i<bl; i=i+1) begin
                dm_fifo[2*rl + i] = dm >> (i*MAX_DIMM_DM_BITS);
                dq_fifo[2*rl + i] = dq >> (i*MAX_DIMM_DQ_BITS);
            end
        end
        join_none
    endtask

    function [MAX_DIMM_DQ_BITS*MAX_BURST_LEN-1:0] BurstOrderData(input [MAX_DIMM_DQ_BITS*MAX_BURST_LEN-1:0] sequential_data_start_0,
                                                            input [MAX_COL_ADDR_BITS-1:0] col, input int burst_length, input UTYPE_bt burst_type);
        reg [MAX_COL_ADDR_BITS-1:0] col_out;
        reg [MAX_COL_ADDR_BITS-1:0] col_out0;
        reg [MAX_COL_ADDR_BITS-1:0] col_out1;

        BurstOrderData = sequential_data_start_0;
        for (int i=0;i<burst_length/2;i++) begin
            col_out = ((col % burst_length) ^ 2*i) & (burst_length-1); // wrapped and masked
            // even bursts are the same w/ SEQ or INT
            if(col_out % 2 == 0) begin
                col_out0 = col_out;
                col_out1 = col_out + 1;
            // odd bursts vary between SEQ and INT
            end else begin
                col_out0 = col_out;
                if(burst_type == SEQ) begin
                    col_out1 = col_out;
                    col_out1[1:0] = col_out + 1;
                end else begin
                    col_out1 = col_out - 1;
                end
            end
            for (int j=0; j<MAX_DIMM_DQ_BITS; j++) begin
                BurstOrderData[j+2*(i)*MAX_DIMM_DQ_BITS] = sequential_data_start_0[j+(col_out0*MAX_DIMM_DQ_BITS)];
                BurstOrderData[j+(2*(i)+1)*MAX_DIMM_DQ_BITS] = sequential_data_start_0[j+(col_out1*MAX_DIMM_DQ_BITS)];
            end
        end
        return BurstOrderData;
    endfunction

    // Receiver(s) for data_verify process
    dqrx dqrx[MAX_DIMM_DQS_BITS-1:0] (ptr_rst_n, idimm.DQS_t, idimm.DQ, q0, q1, q2, q3);

    // Perform data verification as idimm.ADDR result of read_verify task call
    always @(clk_val) begin:data_verify
        reg [MAX_DIMM_DQ_BITS-1:0] bit_mask;
        reg [MAX_DIMM_DM_BITS-1:0] dm_temp;
        reg [MAX_DIMM_DQ_BITS-1:0] dq_temp;

        for (int i = !clk_val; (i < 2/(2.0 - !clk_val)); i=i+1) begin
            if (dm_fifo[i] === {MAX_DIMM_DM_BITS{1'bx}}) begin
                burst_cntr = 0;
            end else begin
                dm_temp = dm_fifo[i];
                for (int j=0; j<MAX_DIMM_DQ_BITS; j=j+1) begin
                    bit_mask[j] = !dm_temp[j/(MAX_DIMM_DQ_BITS/MAX_DIMM_DM_BITS)];
                end
                bit_mask = bit_mask & _dut_config.dq_mask;
                case (burst_cntr)
                    0: dq_temp = q0;
                    1: dq_temp = q1;
                    2: dq_temp = q2;
                    3: dq_temp = q3;
                endcase
                //if (((dq_temp & bit_mask) === (dq_fifo[i] & bit_mask)))
                //    $display ("%m at time %t: INFO: Successful read data compare.  Expected = %h, Actual = %h, Mask = %h, i = %d", $time, dq_fifo[i], dq_temp, bit_mask, burst_cntr);
                if ((dq_temp & bit_mask) !== (dq_fifo[i] & bit_mask)) begin
                    $display("%m @%0t:ERROR: Read data miscompare. Expected:%0h Actual:%0h Mask:%0h Burst:%0d",
                             $time, dq_fifo[i], dq_temp, bit_mask, burst_cntr);
                end
                burst_cntr = burst_cntr + 1;
            end
        end

        if (!clk_val) begin
            ptr_rst_n <= (dm_fifo[4] !== {MAX_DIMM_DM_BITS{1'bx}});
            for (int i=0; i<=(4*MAX_RL+MAX_BURST_LEN); i=i+1) begin
                dm_fifo[i] = dm_fifo[i+2];
                dq_fifo[i] = dq_fifo[i+2];
            end
            odt_fifo = odt_fifo>>1;
        end
    end

    // End-of-test triggered in 'subtest.vh'
    task test_done;
        begin
            $display ("%m at time %0t: INFO: Simulation is Complete", $time);
            $finish(0);
        end
    endtask

    function int GetWidth();
        return _dut_config.by_mode;
    endfunction

    // Test included from external file
    `include "dimm_subtest.vh"

endmodule

module dqrx (
    ptr_rst_n, dqs, dq, q0, q1, q2, q3
);
    import arch_package::*;
    input  ptr_rst_n;
    input  dqs;
    int tDQSCK, tDQSQ;
    `ifdef DDR4_X4
        input [3:0] dq;
    `endif
    `ifdef DDR4_X8
        input [7:0] dq;
    `endif
    `ifdef DDR4_X16
        input [15:0] dq;
    `endif
    output [MAX_DIMM_DQ_BITS/MAX_DIMM_DQS_BITS-1:0] q0;
    output [MAX_DIMM_DQ_BITS/MAX_DIMM_DQS_BITS-1:0] q1;
    output [MAX_DIMM_DQ_BITS/MAX_DIMM_DQS_BITS-1:0] q2;
    output [MAX_DIMM_DQ_BITS/MAX_DIMM_DQS_BITS-1:0] q3;
    reg [MAX_DIMM_DQ_BITS/MAX_DIMM_DQS_BITS-1:0] q [3:0];
    reg [1:0] ptr;

    initial begin
        tDQSCK = 0;
        tDQSQ = 0;
    end

    reg ptr_rst_dly_n;
    always @(ptr_rst_n) ptr_rst_dly_n <= #(tDQSCK + tDQSQ + 2) ptr_rst_n;

    reg dqs_dly;
    always @(dqs) dqs_dly <= #(tDQSQ + 1) dqs;

    always @(negedge ptr_rst_dly_n or posedge dqs_dly or negedge dqs_dly) begin
        if (!ptr_rst_dly_n) begin
            ptr <= 0;
        end else if (dqs_dly || ptr) begin
            q[ptr] <= dq;
            ptr <= ptr + 1;
        end
    end

    assign q0 = q[0];
    assign q1 = q[1];
    assign q2 = q[2];
    assign q3 = q[3];
endmodule
