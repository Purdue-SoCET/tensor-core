/****************************************************************************************
*
*    File Name:  subtest.vh
*
*  Description:  Micron SDRAM DDR4 (Double Data Rate 4)
*                This file is included by tb.v
*
*   Disclaimer   This software code and all associated documentation, comments or other
*  of Warranty:  information (collectively "Software") is provided "AS IS" without
*                warranty of any kind. MICRON TECHNOLOGY, INC. ("MTI") EXPRESSLY
*                DISCLAIMS ALL WARRANTIES EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
*                TO, NONINFRINGEMENT OF THIRD PARTY RIGHTS, AND ANY IMPLIED WARRANTIES
*                OF MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. MTI DOES NOT
*                WARRANT THAT THE SOFTWARE WILL MEET YOUR REQUIREMENTS, OR THAT THE
*                OPERATION OF THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE.
*                FURTHERMORE, MTI DOES NOT MAKE ANY REPRESENTATIONS REGARDING THE USE OR
*                THE RESULTS OF THE USE OF THE SOFTWARE IN TERMS OF ITS CORRECTNESS,
*                ACCURACY, RELIABILITY, OR OTHERWISE. THE ENTIRE RISK ARISING OUT OF USE
*                OR PERFORMANCE OF THE SOFTWARE REMAINS WITH YOU. IN NO EVENT SHALL MTI,
*                ITS AFFILIATED COMPANIES OR THEIR SUPPLIERS BE LIABLE FOR ANY DIRECT,
*                INDIRECT, CONSEQUENTIAL, INCIDENTAL, OR SPECIAL DAMAGES (INCLUDING,
*                WITHOUT LIMITATION, DAMAGES FOR LOSS OF PROFITS, BUSINESS INTERRUPTION,
*                OR LOSS OF INFORMATION) ARISING OUT OF YOUR USE OF OR INABILITY TO USE
*                THE SOFTWARE, EVEN IF MTI HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH
*                DAMAGES. Because some jurisdictions prohibit the exclusion or
*                limitation of liability for consequential or incidental damages, the
*                above limitation may not apply to you.
*
*                Copyright 2003 Micron Technology, Inc. All rights reserved.
*
****************************************************************************************/

    initial begin : test
        UTYPE_TS min_ts, nominal_ts, max_ts;
        reg [MAX_BURST_LEN*MAX_DQ_BITS-1:0] b0to7, b8tof, b7to0, bfto8;
        reg [MODEREG_BITS-1:0] mode_regs[MAX_MODEREGS];
        UTYPE_DutModeConfig dut_mode_config;
        bit failure;

        min_ts = TS_750;
        nominal_ts = TS_1250;
        max_ts = TS_1500;
        b0to7 = { {MAX_DQ_BITS/4{4'h7}}, {MAX_DQ_BITS/4{4'h6}}, {MAX_DQ_BITS/4{4'h5}}, {MAX_DQ_BITS/4{4'h4}},
                  {MAX_DQ_BITS/4{4'h3}}, {MAX_DQ_BITS/4{4'h2}}, {MAX_DQ_BITS/4{4'h1}}, {MAX_DQ_BITS/4{4'h0}} };
        b8tof = { {MAX_DQ_BITS/4{4'hf}}, {MAX_DQ_BITS/4{4'he}}, {MAX_DQ_BITS/4{4'hd}}, {MAX_DQ_BITS/4{4'hc}},
                  {MAX_DQ_BITS/4{4'hb}}, {MAX_DQ_BITS/4{4'ha}}, {MAX_DQ_BITS/4{4'h9}}, {MAX_DQ_BITS/4{4'h8}} };
        b7to0 = { {MAX_DQ_BITS/4{4'h0}}, {MAX_DQ_BITS/4{4'h1}}, {MAX_DQ_BITS/4{4'h2}}, {MAX_DQ_BITS/4{4'h3}},
                  {MAX_DQ_BITS/4{4'h4}}, {MAX_DQ_BITS/4{4'h5}}, {MAX_DQ_BITS/4{4'h6}}, {MAX_DQ_BITS/4{4'h7}} };
        bfto8 = { {MAX_DQ_BITS/4{4'h8}}, {MAX_DQ_BITS/4{4'h9}}, {MAX_DQ_BITS/4{4'ha}}, {MAX_DQ_BITS/4{4'hb}},
                  {MAX_DQ_BITS/4{4'hc}}, {MAX_DQ_BITS/4{4'hd}}, {MAX_DQ_BITS/4{4'he}}, {MAX_DQ_BITS/4{4'hf}} };
        iDDR4.RESET_n <= 1'b1;
        iDDR4.CKE <= 1'b0;
        iDDR4.CS_n  <= 1'b1;
        iDDR4.ACT_n <= 1'b1;
        iDDR4.RAS_n_A16 <= 1'b1;
        iDDR4.CAS_n_A15 <= 1'b1;
        iDDR4.WE_n_A14 <= 1'b1;
        iDDR4.BG <= '1;
        iDDR4.BA <= '1;
        iDDR4.ADDR <= '1;
        iDDR4.ADDR_17 <= '0;
        iDDR4.ODT <= 1'b0;
        iDDR4.PARITY <= 0;
        iDDR4.ALERT_n <= 1;
        iDDR4.PWR <= 0;
        iDDR4.TEN <= 0;
        iDDR4.VREF_CA <= 0;
        iDDR4.VREF_DQ <= 0;
        iDDR4.ZQ <= 0;
        dq_en <= 1'b0;
        dqs_en <= 1'b0;

        default_period(nominal_ts);

        // POWERUP SECTION
        power_up();

        // Reset DLL
        dut_mode_config = _state.DefaultDutModeConfig(.cl(12),
                                                      .write_recovery(14),
                                                      .qoff(0),
                                                      .cwl(10),
                                                      .wr_preamble_clocks(2),
                                                      .bl_reg(rBLFLY),
                                                      .dll_enable(1),
                                                      .dll_reset(1));
        _state.ModeToAddrDecode(dut_mode_config, mode_regs);
        load_mode(.bg(0), .ba(1), .addr(mode_regs[1]));
        deselect(timing.tDLLKc);

        dut_mode_config.DLL_reset = 0;
        _state.ModeToAddrDecode(dut_mode_config, mode_regs);

        load_mode(.bg(0), .ba(3), .addr(mode_regs[3]));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(1), .ba(2), .addr(mode_regs[6]));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(1), .ba(1), .addr(mode_regs[5]));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(1), .ba(0), .addr(mode_regs[4]));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(0), .ba(2), .addr(mode_regs[2]));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(0), .ba(1), .addr(mode_regs[1]));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(0), .ba(0), .addr(mode_regs[0]));
        deselect(timing.tMOD/timing.tCK);
        zq_cl();
        deselect(timing.tZQinitc);

        odt_out <= 1;                           // turn on odt

        activate(.bg(0), .ba(0), .row(0));                         // Activate Bank 0, Row 0
        deselect(timing.tRCD/timing.tCK);
        $display("Consecutive WRITE (BL8) to WRITE (BL8)");
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(1), .dm('1), .dq('0 | {MAX_DQ_BITS{1'b1}}));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(1), .dm('1), .dq('0 | ({MAX_DQ_BITS{1'b1}} << MAX_DQ_BITS)));
        $display("Consecutive WRITE (BL4) to WRITE (BL4)");
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(0), .dm('1), .dq('0 | ({MAX_DQ_BITS{1'b1}} << MAX_DQ_BITS*2)));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(0), .dm('1), .dq('0 | ({MAX_DQ_BITS{1'b1}} << MAX_DQ_BITS*3)));
        $display("WRITE (BL4 on the fly) to READ (BL4 on the fly)");
        deselect(_dut_mode_config.WL_calculated + 4 + timing.tWTR_L/timing.tCK);
        read_verify(.bg(0), .ba(0), .col(0), .ap(0), .bc(0), .dm(0), .dq('0 | ({MAX_DQ_BITS{1'b1}} << MAX_DQ_BITS*3)));
        deselect(_dut_mode_config.RL + timing.tCCD_L/timing.tCK + _dut_mode_config.BL/2 + _dut_mode_config.wr_preamble_clocks - _dut_mode_config.WL_calculated);
        $display("READ (BL4) to WRITE (BL8)");
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(1), .dm('1), .dq('0 | {MAX_DQ_BITS{1'b1}}));
        deselect(_dut_mode_config.WL_calculated + 4 + timing.tWTR_L/timing.tCK);
        $display("WRITE (BL8) to READ (BL4)");
        read_verify(.bg(0), .ba(0), .col(0), .ap(0), .bc(0), .dm(0), .dq('0 | {MAX_DQ_BITS{1'b1}}));
        deselect(_dut_mode_config.RL + timing.tCCD_L/timing.tCK  + _dut_mode_config.BL/2 + _dut_mode_config.wr_preamble_clocks - _dut_mode_config.WL_calculated);
        $display("READ (BL4) to WRITE (BL4)");
        read(.bg(0), .ba(0), .col(0), .ap(0), .bc(0));
        deselect(_dut_mode_config.RL + timing.tCCD_L/timing.tCK  + _dut_mode_config.BL/2 + _dut_mode_config.wr_preamble_clocks - _dut_mode_config.WL_calculated);
        write(.bg(0), .ba(0), .col(0), .ap(1), .bc(0), .dm('1), .dq('1));
        deselect(_dut_mode_config.WL_calculated + 4 + _dut_mode_config.write_recovery);
        deselect(timing.tRP/timing.tCK);

        $display("tRRD Timing");
        activate(.bg(0), .ba(0), .row(0));
        deselect(timing.tRRD_L/timing.tCK);
        activate(.bg(0), .ba(1), .row(0));
        deselect(timing.tRRD_L/timing.tCK);
        activate(.bg(0), .ba(2), .row(0));
        deselect(timing.tRRD_L/timing.tCK);
        activate(.bg(0), .ba(3), .row(0));
        deselect(timing.tRCD/timing.tCK);

        $display("Consecutive Writes");
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(1), .dm('1), .dq(b0to7));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(1), .col(0), .ap(0), .bc(1), .dm('1), .dq(b8tof));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(2), .col(0), .ap(0), .bc(1), .dm('1), .dq(b7to0));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(3), .col(0), .ap(0), .bc(1), .dm('1), .dq(bfto8));
        deselect(_dut_mode_config.WL_calculated + _dut_mode_config.BL/2 + timing.tWTR_L/timing.tCK + _dut_mode_config.write_recovery);

        $display("Consecutive Reads");
        read_verify(.bg(0), .ba(0), .col(0), .ap(0), .bc(1), .dm(0), .dq(b0to7));
        deselect(timing.tCCD_L/timing.tCK);
        read_verify(.bg(0), .ba(1), .col(0), .ap(0), .bc(1), .dm(0), .dq(b8tof));
        deselect(timing.tCCD_L/timing.tCK);
        read_verify(.bg(0), .ba(2), .col(0), .ap(0), .bc(1), .dm(0), .dq(b7to0));
        deselect(timing.tCCD_L/timing.tCK);
        read_verify(.bg(0), .ba(3), .col(0), .ap(0), .bc(1), .dm(0), .dq(bfto8));
        deselect(timing.tCCD_L/timing.tCK + _dut_mode_config.RL + _dut_mode_config.BL/2);

        $display("Non Consecutive Writes");
        write(.bg(0), .ba(0), .col(0), .ap(0), .bc(1), .dm('1), .dq(b0to7));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(1), .col(0), .ap(0), .bc(1), .dm('1), .dq(b8tof));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(2), .col(0), .ap(0), .bc(1), .dm('1), .dq(b7to0));
        deselect(timing.tCCD_L/timing.tCK);
        write(.bg(0), .ba(3), .col(0), .ap(0), .bc(1), .dm('1), .dq(bfto8));
        deselect(_dut_mode_config.WL_calculated + _dut_mode_config.BL/2 + timing.tWTR_L/timing.tCK + _dut_mode_config.write_recovery);

        $display("Non Consecutive Reads");
        read_verify(.bg(0), .ba(0), .col(0), .ap(1), .bc(1), .dm(0), .dq(b0to7));
        deselect(timing.tCCD_L/timing.tCK);
        read_verify(.bg(0), .ba(1), .col(0), .ap(1), .bc(1), .dm(0), .dq(b8tof));
        deselect(timing.tCCD_L/timing.tCK);
        read_verify(.bg(0), .ba(2), .col(0), .ap(1), .bc(1), .dm(0), .dq(b7to0));
        deselect(timing.tCCD_L/timing.tCK);
        read_verify(.bg(0), .ba(3), .col(0), .ap(1), .bc(1), .dm(0), .dq(bfto8));
        deselect(_dut_mode_config.AL + timing.tRTP/timing.tCK + timing.tRP/timing.tCK);

        for (UTYPE_TS ts = min_ts.first(); ts < min_ts.last(); ts = ts.next()) begin
            if (1 == tt_timesets[ts][TS_LOADED]) begin
                sr_change_period(ts);
            end
        end

        sr_change_period(nominal_ts);
        deselect(10);
        // POWER DOWN SECTION
        odt_out <= 1'b0;
        odt_out <= #(50*timing.tCK) 1'b1;
        odt_out <= #((50 + MAX_BL)*timing.tCK) 1'b0;
        refresh();
        deselect(timing.tREFPDENc);
        precharge_power_down(timing.tRFC/timing.tCK);
        deselect(timing.tXSDLLc);
        self_refresh(timing.tRFC/timing.tCK);
        deselect(timing.tDLLKc);

        $display("Power-Down Entry after WRITE w/ AP (WRA)");
        dut_mode_config.BL_reg = rBL4;
        _state.ModeToAddrDecode(dut_mode_config, mode_regs);
        load_mode(.bg(0), .ba(0), .addr(mode_regs[0])); // Mode Register with Burst Chop

        deselect(timing.tMOD/timing.tCK);
        activate(.bg(0), .ba(0), .row(0)); // Activate Bank 0, Row 0
        deselect(timing.tRCD/timing.tCK);
        write(.bg(0), .ba(0), .col(0), .ap(1), .bc(0), .dm('1), .dq('0 | {MAX_DQ_BITS{1'b1}}));
        deselect(_dut_mode_config.WL_calculated + 5 + _dut_mode_config.write_recovery);
        active_power_down(timing.tPDc);
        deselect(timing.tXSc);

        $display("refresh to power down re-entry");
        refresh();
        deselect(timing.tREFPDENc);
        precharge_power_down(timing.tPDc);
        deselect(timing.tXSDLLc);
        precharge_power_down(timing.tPDc);
        deselect(timing.tXSDLLc);

        $display("Power-Down Exit to Refresh to Power-Down Entry");
        refresh();
        deselect(timing.tREFPDENc);
        precharge_power_down(timing.tPDc);
        deselect(timing.tXSDLLc);

        $display("Change Frequency to %s during Self Refresh", max_ts.name());
        sr_change_period(max_ts);
        deselect(timing.tXSDLLc);

        $display("Change Frequency to %s during Self Refresh", min_ts.name());
        sr_change_period(min_ts);
        deselect(timing.tXSDLLc);

        $display("Change Frequency to %s during Self Refresh", min_ts.name());
        sr_change_period(nominal_ts);
        deselect(timing.tXSDLLc);

        // TODO: multipurpose register section

        // self refresh with ck off
        deselect(timing.tMOD/timing.tCK);
        self_refresh(timing.tCKSREc);
        clk_enb = 0;
        #(timing.tRFC);
        clk_enb <= 1'b1;
        #(timing.tCKSRX);
        deselect(timing.tXSDLLc + 1);

        // Gear down
        _state.ModeToAddrDecode(dut_mode_config, mode_regs);
        load_mode(.bg(0), .ba(0), .addr((mode_regs[0] & ~'he00) | 'h600));
        deselect(timing.tMOD/timing.tCK);
        load_mode(.bg(0), .ba(3), .addr(mode_regs[3] | 'h8 | 'h4));
        deselect(timing.tSYNC_GEARc);
        nop(1);
        deselect(timing.tCMD_GEARc + 1);
        activate(.bg('b1), .ba('b11), .row('b1010));
        deselect(timing.tSYNC_GEARc);

        // TODO: write levelization section

        // TODO: zq_calibration

        // Setting a fixed timeset can also be accomplished using +define+FIXED_2400 (for example) see readme.txt for all options.
        $display("Forcing model configuration");
        // Setting the correct timeset.
        sr_change_period(TS_833);
        SetTimingStruct(TS_833);
        timing.tCK = tCK;
        _state.UpdateTiming(timing);
        deselect(timing.tXSDLLc);
        golden_model.set_timing_parameter_lock(.locked(1), .recalculate_params(1), .non_spec_tck(833)); // Prevent tCK changes from changing the loaded timeset.
        // Forcing dut mode config parameters without loadmodes.
        // Please see arch_package.sv::UTYPE_DutModeConfig for settings.
        // Be careful since there are many illegal configurations.
        // Many parameters are enumerated values, please see arch_package.sv::UTYPE_DutModeConfig.
        dut_mode_config.CL = 18;
        dut_mode_config.CWL = 14;
        dut_mode_config.BL_reg = rBL8;
        dut_mode_config.write_recovery = 20;
        dut_mode_config.rd_preamble_clocks = 2;
        // Forcing the model.
        golden_model.SetDutModeConfig(dut_mode_config);

        // Initializing memory with a file.
        $display("Reading memory initialized with a file");
        failure = golden_model.initialize_memory_with_file("memory_file.txt");
        activate(.bg(0), .ba(0), .row(0));
        deselect(timing.tRCD/timing.tCK);
        activate(.bg(1), .ba(1), .row(0));
        deselect(timing.tRCD/timing.tCK);
        activate(.bg(0), .ba(1), .row(0));
        deselect(timing.tRCD/timing.tCK);
        read(.bg(0), .ba(0), .col(0), .ap(1));
        deselect(_dut_mode_config.RL + timing.tCCD_L/timing.tCK + _dut_mode_config.BL/2 + _dut_mode_config.wr_preamble_clocks - _dut_mode_config.WL_calculated);
//         read(.bg(1), .ba(1), .col(0), .ap(1));
        deselect(_dut_mode_config.RL + timing.tCCD_L/timing.tCK + _dut_mode_config.BL/2 + _dut_mode_config.wr_preamble_clocks - _dut_mode_config.WL_calculated);
        read(.bg(0), .ba(1), .col(0), .ap(1));
        deselect(_dut_mode_config.RL + _dut_mode_config.BL/2 + timing.tRAS/timing.tCK);

        // Accessing memory with a function.
        // bg/ba/row/col are not limited by the current configuration. Please make sure they are correct.
        for (int i=0;i<64;i++) begin
            logic[MAX_DQ_BITS*MAX_BURST_LEN-1:0] data;

            data = {$urandom, $urandom, $urandom, $urandom};
            failure = golden_model.memory_write(.bg(i[3:2]), .ba(i[1:0]), .row(i+2*i), .col(i+i), .data(data));
            // for 3DS
            // failure = golden_model.memory_write_with_rank(.rank(0), .bg(i[3:2]), .ba(i[1:0]), .row(i+2*i), .col(i+i), .data(data));
            $display("Writing [%0d][%0d][%0h][%0h] %0h", i[3:2], i[1:0], i+2*i, i+i, data);
            data = '1;
            failure = golden_model.memory_read(.bg(i[3:2]), .ba(i[1:0]), .row(i+2*i), .col((i+i) & ~'h3), .data(data));
            // for 3DS
            // failure = golden_model.memory_read_with_rank(.rank(0), .bg(i[3:2]), .ba(i[1:0]), .row(i+2*i), .col((i+i) & ~'h3), .data(data));
            $display("Reading [%0d][%0d][%0h][%0h] %0h", i[3:2], i[1:0], i+2*i, i+i, data);
            activate(.bg(i[3:2]), .ba(i[1:0]), .row(i+2*i));
            deselect(timing.tRCD/timing.tCK);
            read(.bg(i[3:2]), .ba(i[1:0]), .col((i+i) & ~'h3), .ap(1));
            deselect(_dut_mode_config.RL + _dut_mode_config.BL + timing.tRAS/timing.tCK);
            precharge(.ap(1));
            deselect(timing.tRAS/timing.tCK);
        end

        test_done;
    end
