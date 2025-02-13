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
module tb;
    timeunit 1ps;
    timeprecision 1ps;
    import arch_package::*;
    import proj_package::*;
    StateTable _state();
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
    `ifdef DDR4_X4
        DDR4_if #(.CONFIGURED_DQ_BITS(4)) iDDR4();
    `endif
    `ifdef DDR4_X8
        DDR4_if #(.CONFIGURED_DQ_BITS(8)) iDDR4();
    `endif
    `ifdef DDR4_X16
        DDR4_if #(.CONFIGURED_DQ_BITS(16)) iDDR4();
    `endif
    reg clk_val, clk_enb;
    bit[159:0] func_str;
    UTYPE_dutconfig _dut_config;
    DDR4_cmd active_cmd = new();
    UTYPE_TimingParameters timing;
    wire model_enable;
    reg model_enable_val;
    wire odt_wire;
    UTYPE_cmdtype driving_cmd;

    // DQ transmit
    reg dq_en;
    reg dqs_en;
    reg[MAX_DQ_BITS-1:0] dq_out;
    reg[MAX_DQS_BITS-1:0] dqs_out;
    reg[MAX_DM_BITS-1:0] dm_out;
    assign iDDR4.DM_n = dq_en ? dm_out : {MAX_DM_BITS{1'bz}};
    assign iDDR4.DQ = dq_en ? dq_out : {MAX_DQ_BITS{1'bz}};
    assign iDDR4.DQS_t = dqs_en ? dqs_out : {MAX_DQS_BITS{1'bz}};
    assign iDDR4.DQS_c = dqs_en ? ~dqs_out : {MAX_DQS_BITS{1'bz}};

    assign model_enable = model_enable_val;

    // DQ receive
    reg[MAX_DM_BITS-1:0] dm_fifo [4*(MAX_RL+MAX_BURST_LEN+MAX_CAL):0];
    reg[MAX_DQ_BITS-1:0] dq_fifo [4*(MAX_RL+MAX_BURST_LEN+MAX_CAL):0];
    wire[MAX_DQ_BITS-1:0] q0, q1, q2, q3;
    reg ptr_rst_n;
    reg[1:0] burst_cntr;

    reg odt_out;
    reg[MAX_RL:0] odt_fifo;
//     assign iDDR4.ODT = odt_out & !odt_fifo[0];

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
    `ifdef DDR4_STACK_X4_2H
        parameter int CONFIGURED_DQ_BITS = 4;
        parameter int CONFIGURED_RANKS = 2;
    `endif
    `ifdef DDR4_STACK_X8_2H
        parameter int CONFIGURED_DQ_BITS = 8;
        parameter int CONFIGURED_RANKS = 2;
    `endif
    `ifdef DDR4_STACK_X16_2H
        parameter int CONFIGURED_DQ_BITS = 16;
        parameter int CONFIGURED_RANKS = 2;
    `endif
    `ifdef DDR4_STACK_X4_4H
        parameter int CONFIGURED_DQ_BITS = 4;
        parameter int CONFIGURED_RANKS = 4;
    `endif
    `ifdef DDR4_STACK_X8_4H
        parameter int CONFIGURED_DQ_BITS = 8;
        parameter int CONFIGURED_RANKS = 4;
    `endif
    `ifdef DDR4_STACK_X16_4H
        parameter int CONFIGURED_DQ_BITS = 16;
        parameter int CONFIGURED_RANKS = 4;
    `endif
    initial begin
        $timeformat (-9, 1, " ns", 1);
        _dut_config.by_mode = CONFIGURED_DQ_BITS;
        _dut_config.density = CONFIGURED_DENSITY;
        _dut_config.ranks = CONFIGURED_RANKS;
        arch_package::dut_config_populate(_dut_config);
        proj_package::project_dut_config(_dut_config);
        _state.Initialize("tb", _dut_config, 0);
        iDDR4.CK <= 2'b01;
        clk_enb <= 1'b1;
        clk_val <= 1'b1;
        odt_fifo <= 0;
        model_enable_val = 1;
    end

    always @(active_cmd.cmd) begin
        driving_cmd = active_cmd.cmd;
    end
    // Component instantiation
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_DENSITY(CONFIGURED_DENSITY), .CONFIGURED_RANKS(CONFIGURED_RANKS))
                 golden_model(.model_enable(model_enable), .iDDR4(iDDR4));
    // Clock generator
    always @(posedge clk_val && clk_enb) begin
      clk_val <= #(timing.tCK/2) 1'b0;
      clk_val <= #(timing.tCK) 1'b1;
      iDDR4.CK[1] <= #(timing.tCK/2) 1'b0;
      iDDR4.CK[1] <= #(timing.tCK) 1'b1;
      iDDR4.CK[0] <= #(timing.tCK/2) 1'b1;
      iDDR4.CK[0] <= #(timing.tCK) 1'b0;
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
        iDDR4.CS_n = 1'b0;
        iDDR4.ACT_n <= 1;
        iDDR4.RAS_n_A16 <= 1;
        iDDR4.CAS_n_A15 <= 1;
        iDDR4.WE_n_A14 <= 1;
        iDDR4.CKE <= 0;
        iDDR4.TEN <= 0;
        iDDR4.PARITY <= 0;
        iDDR4.ALERT_n <= 1;
        iDDR4.RESET_n <= 0;
        iDDR4.ZQ <= 0;
        iDDR4.PWR <= 0;
        iDDR4.VREF_CA <= 0;
        iDDR4.VREF_DQ <= 0;
        #(timing.tRESET);
        iDDR4.PWR <= 1;
        iDDR4.VREF_CA <= 1;
        iDDR4.VREF_DQ <= 1;
        #(timing.tPWRUP);
        iDDR4.RESET_n <= 1;

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
        iDDR4.CKE <= 1'b0;
        iDDR4.CS_n  <= 1'b1;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdPPDE;
        active_cmd.tCK = timing.tCK;
        _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task active_power_down(int count);
        func_str = "active_power_down";
        iDDR4.CKE <= 1'b0;
        iDDR4.CS_n  <= 1'b1;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdAPDE;
        active_cmd.tCK = timing.tCK;
        _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task load_mode(reg[MAX_BANK_GROUP_BITS-1:0] bg,
                   reg[MAX_BANK_BITS-1:0] ba,
                   reg[MODEREG_BITS-1:0] addr);
        func_str = "load_mode";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b0;
        iDDR4.CAS_n_A15 <= 1'b0;
        iDDR4.WE_n_A14  <= 1'b0;
        iDDR4.BG <= bg;
        iDDR4.BA <= ba;
        iDDR4.ADDR <= addr;
        active_cmd.Populate(cmdLMR, '0, bg, ba, addr[13:0], timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    task refresh(reg[MAX_RANK_BITS-1:0] rank = '0, reg[MAX_BANK_GROUP_BITS-1:0] bg = 0, reg[MAX_BANK_BITS-1:0] ba = 0);
        func_str = "refresh";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b0;
        iDDR4.CAS_n_A15 <= 1'b0;
        iDDR4.WE_n_A14  <= 1'b1;
        iDDR4.BG  <= bg;
        iDDR4.BA  <= ba;
        active_cmd.Populate(cmdREF, rank, bg, ba, iDDR4.ADDR, timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    task precharge(reg[MAX_RANK_BITS-1:0] rank = '0,
                   reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
                   reg[MAX_BANK_BITS-1:0] ba = '0,
                   bit ap = 0); // Precharge all
        func_str = "precharge";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b0;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b0;
        iDDR4.BG  <= bg;
        iDDR4.BA  <= ba;
        iDDR4.ADDR <= (ap<<10);
        active_cmd.Populate(cmdPRE, rank, bg, ba, (ap<<AUTOPRECHARGEADDR), timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    task activate(reg[MAX_RANK_BITS-1:0] rank = '0,
                  reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
                  reg[MAX_BANK_BITS-1:0] ba = '0,
                  reg[MAX_ROW_ADDR_BITS-1:0] row = '0);
        func_str = "activate";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n <= 1'b0;
        iDDR4.ACT_n <= 1'b0;
        iDDR4.RAS_n_A16 <= row[16];
        iDDR4.CAS_n_A15 <= row[15];
        iDDR4.WE_n_A14 <= row[14];
        iDDR4.BG <= bg;
        iDDR4.BA <= ba;
        iDDR4.ADDR <= row;
        active_cmd.Populate(cmdACT, rank, bg, ba, row, timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    // Write task supports burst lengths <= 8
    task write(reg[MAX_RANK_BITS-1:0] rank = '0,
               reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
               reg[MAX_BANK_BITS-1:0] ba = '0,
               reg[MAX_COL_ADDR_BITS-1:0] col = '0,
               bit ap = 0, // Auto Precharge
               bit bc = 0, // Burst Chop
               reg[MAX_BURST_LEN*MAX_DM_BITS-1:0] dm = '0,
               reg[MAX_BURST_LEN*MAX_DQ_BITS-1:0] dq = '0
               );
        int wl, bl;
        reg[MAX_ADDR_BITS-1:0] drive_addr[2:0];

        func_str = "write";
        drive_addr[0] = col & _dut_config.col_mask; // addr[9:0] = COL[9:0]
        drive_addr[1] = ((col >> 10) & 1'h1) << 11; // addr[11] = COL[10]
        drive_addr[2] = (col >> 11) << 13;         // addr[N:13] = COL[N:11]
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b0;
        iDDR4.WE_n_A14  <= 1'b0;
        iDDR4.BG  <= bg;
        iDDR4.BA  <= ba;
        iDDR4.ADDR <= drive_addr[0] | drive_addr[1] | drive_addr[2] |
                      (ap << AUTOPRECHARGEADDR) | (bc << BLFLYSELECT);

        wl = _dut_mode_config.WL_calculated;
        bl = _state.CheckFlyBL(bc << BLFLYSELECT);
        dqs_en <= #(wl*timing.tCK-(timing.tCK*_dut_mode_config.wr_preamble_clocks)) 1'b1;
        dqs_out <= #(wl*timing.tCK-(timing.tCK*_dut_mode_config.wr_preamble_clocks)) {MAX_DQS_BITS{1'b1}};
        for (int i=0; i<=bl; i++) begin
            dqs_en <= #(wl*timing.tCK + i*timing.tCK/2) 1'b1;
            if (i%2 == 0) begin
                dqs_out <= #(wl*timing.tCK + i*timing.tCK/2) {MAX_DQS_BITS{1'b0}};
            end else begin
                dqs_out <= #(wl*timing.tCK + i*timing.tCK/2) {MAX_DQS_BITS{1'b1}};
            end

            dq_en  <= #(wl*timing.tCK + i*timing.tCK/2 + timing.tCK/4) 1'b1;
            dm_out <= #(wl*timing.tCK + i*timing.tCK/2 + timing.tCK/4) dm>>i*MAX_DM_BITS;
            dq_out <= #(wl*timing.tCK + i*timing.tCK/2 + timing.tCK/4) dq>>i*MAX_DQ_BITS;
        end
        dqs_en <= #(wl*timing.tCK + bl*timing.tCK/2 + timing.tCK/2) 1'b0;
        dq_en  <= #(wl*timing.tCK + bl*timing.tCK/2 + timing.tCK/4) 1'b0;
        active_cmd.Populate(cmdWR, rank, bg, ba, col, timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    // Read without data verification
    task read(reg[MAX_RANK_BITS-1:0] rank = '0,
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
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b0;
        iDDR4.WE_n_A14  <= 1'b1;
        iDDR4.BG  <= bg;
        iDDR4.BA  <= ba;
        iDDR4.ADDR <= drive_addr[0] | drive_addr[1] | drive_addr[2] |
                      (ap << AUTOPRECHARGEADDR) | (bc << BLFLYSELECT);

        wl = _dut_mode_config.WL_calculated;
        rl = _dut_mode_config.RL;
        bl = _state.CheckFlyBL(bc << BLFLYSELECT);

        for (int i=0; i<(bl/2 + 2); i=i+1) begin
            odt_fifo[rl-wl + i] = 1'b1;
        end
        active_cmd.Populate(cmdRD, rank, bg, ba, col, timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    task zq_cs(reg[MAX_ADDR_BITS-1:0] addr = '0);
        func_str = "zq_cs";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b0;
        addr = addr & ~(1'b1 << AUTOPRECHARGEADDR);
        iDDR4.ADDR <= addr;
        active_cmd.Populate(cmdZQ, iDDR4.C, iDDR4.BG, iDDR4.BA, addr, timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    task zq_cl(reg[MAX_ADDR_BITS-1:0] addr = '0);
        func_str = "zq_cs";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b0;
        addr = addr | (1'b1 << AUTOPRECHARGEADDR);
        iDDR4.ADDR <= addr;
        active_cmd.Populate(cmdZQ, iDDR4.C, iDDR4.BG, iDDR4.BA, addr, timing.tCK);
        _state.UpdateTable(active_cmd);
        @(negedge clk_val);
    endtask

    task nop(int count);
        func_str = "nop";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdNOP;
        active_cmd.tCK = timing.tCK;
        repeat(count) _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task deselect(int count);
        func_str = "deselect";
        iDDR4.CKE <= 1'b1;
        iDDR4.CS_n  <= 1'b1;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdNOP;
        active_cmd.tCK = timing.tCK;
        repeat(count) _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task deselect_cs_cke(int count, logic cs, logic cke);
        func_str = "deselect";
        iDDR4.CKE <= cke;
        iDDR4.CS_n  <= cs;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b1;
        active_cmd.cmd = cmdNOP;
        active_cmd.tCK = timing.tCK;
        repeat(count) _state.UpdateTable(active_cmd);
        repeat(count) @(negedge clk_val);
    endtask

    task self_refresh(int count);
        func_str = "self_refresh";
        iDDR4.CKE <= 1'b0;
        iDDR4.CS_n  <= 1'b0;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b0;
        iDDR4.CAS_n_A15 <= 1'b0;
        iDDR4.WE_n_A14  <= 1'b1;
        @(negedge clk_val);
        iDDR4.CS_n  <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14  <= 1'b1;
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
        deselect_cs_cke(.count(timing.tCKSREc), .cs(1), .cke(0));
        SetTimingStruct(new_ts);
        timing.tCK = tCK;
        _state.UpdateTiming(timing);
        deselect_cs_cke(.count(timing.tCKSRXc), .cs(1), .cke(0));
        $display("%m at time %0t: INFO: Changing Clock Period to %s (%0d ps)", $time, new_ts.name(), timing.tCK);
        deselect(.count(timing.tXSc));
        @(negedge clk_val);
    endtask

    // Read with data verification
    task read_verify(reg[MAX_RANK_BITS-1:0] rank = '0,
                     reg[MAX_BANK_GROUP_BITS-1:0] bg = '0,
                     reg[MAX_BANK_BITS-1:0] ba = '0,
                     reg[MAX_COL_ADDR_BITS-1:0] col = '0,
                     bit ap = 0, // Auto Precharge
                     bit bc = 0, // Burst Chop
                     reg[MAX_BURST_LEN*MAX_DM_BITS-1:0] dm = '0, // Expected Data Mask
                     reg[MAX_BURST_LEN*MAX_DQ_BITS-1:0] dq = '0 // Expected Data
                    );
        int rl, bl;

        func_str = "read_verify";
        read(.rank(rank), .bg(bg), .ba(ba), .col(col), .ap(ap), .bc(bc));
        rl = _dut_mode_config.RL;
        bl = _state.CheckFlyBL(bc << BLFLYSELECT);
        dq = BurstOrderData(dq, col, bl, _dut_mode_config.BT);
        fork // this scheduling must take place after current clock falling edge
        begin
            #1;
            for (int i=0; i<bl; i=i+1) begin
                dm_fifo[2*rl + i] = dm >> (i*MAX_DM_BITS);
                dq_fifo[2*rl + i] = dq >> (i*MAX_DQ_BITS);
            end
        end
        join_none
    endtask

    function [MAX_DQ_BITS*MAX_BURST_LEN-1:0] BurstOrderData(input [MAX_DQ_BITS*MAX_BURST_LEN-1:0] sequential_data_start_0,
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
            for (int j=0; j<MAX_DQ_BITS; j++) begin
                BurstOrderData[j+2*(i)*MAX_DQ_BITS] = sequential_data_start_0[j+(col_out0*MAX_DQ_BITS)];
                BurstOrderData[j+(2*(i)+1)*MAX_DQ_BITS] = sequential_data_start_0[j+(col_out1*MAX_DQ_BITS)];
            end
        end
        return BurstOrderData;
    endfunction

    // Receiver(s) for data_verify process
    dqrx dqrx[MAX_DQS_BITS-1:0] (ptr_rst_n, iDDR4.DQS_t, iDDR4.DQ, q0, q1, q2, q3);

    // Perform data verification as iDDR4.ADDR result of read_verify task call
    always @(clk_val) begin:data_verify
        reg [MAX_DQ_BITS-1:0] bit_mask;
        reg [MAX_DM_BITS-1:0] dm_temp;
        reg [MAX_DQ_BITS-1:0] dq_temp;

        for (int i = !clk_val; (i < 2/(2.0 - !clk_val)); i=i+1) begin
            if (dm_fifo[i] === {MAX_DM_BITS{1'bx}}) begin
                burst_cntr = 0;
            end else begin
                dm_temp = dm_fifo[i];
                for (int j=0; j<MAX_DQ_BITS; j=j+1) begin
                    bit_mask[j] = !dm_temp[j/(MAX_DQ_BITS/MAX_DM_BITS)];
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
            ptr_rst_n <= (dm_fifo[4] !== {MAX_DM_BITS{1'bx}});
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
    `include "subtest.vh"

endmodule

module dqrx(ptr_rst_n, dqs, dq, q0, q1, q2, q3);
    timeunit 1ps;
    timeprecision 1ps;
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
    output [MAX_DQ_BITS/MAX_DQS_BITS-1:0] q0;
    output [MAX_DQ_BITS/MAX_DQS_BITS-1:0] q1;
    output [MAX_DQ_BITS/MAX_DQS_BITS-1:0] q2;
    output [MAX_DQ_BITS/MAX_DQS_BITS-1:0] q3;
    reg [MAX_DQ_BITS/MAX_DQS_BITS-1:0] q [3:0];
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
