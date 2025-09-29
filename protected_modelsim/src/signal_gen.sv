`timescale 1ns/1ps
`include "signal_gen_if.vh"

module signal_gen #(

) (
    input logic CLK,
    input logic nRST,
    signal_gen_if.dut mysig
);
    import dram_pkg::*;

    logic nACT_n;
    logic nRAS_n_A16;
    logic nCAS_n_A15;
    logic nWE_n_A14;
    logic nALERT_n;
    logic nPARITY;
    logic nRESET_n;
    logic nTEN;
    logic nCS_n;
    logic nCKE;
    logic nODT;
    logic nZQ;
    logic nPWR;
    logic nVREF_CA;
    logic nVREF_DQ;
    logic [RANK_BITS-1:0] nC;
    logic [BANK_GROUP_BITS-1:0] nBG;
    logic [BANK_BITS-1:0] nBA;

    logic [ADDR_BITS-1:0] nADDR;
    logic nADDR_17;

    logic [4:0] cmd_addr;
    logic issue;

    assign issue = mysig.state != mysig.nstate;


    // always_ff @(posedge CLK, negedge nRST) begin
    //     if (!nRST) begin
    //         mysig.ACT_n          <= 0;
    //         mysig.RAS_n_A16 <= 0;
    //         mysig.CAS_n_A15 <= 0;
    //         mysig.WE_n_A14 <= 0;
    //         mysig.ALERT_n <= 0;
    //         mysig.PARITY <= 0;
    //         mysig.RESET_n <= 0;
    //         mysig.TEN         <= 0;
    //         mysig.CS_n <= 0;
    //         mysig.CKE <= 0;
    //         mysig.ODT <= 0;
    //         mysig.ZQ <= 0;
    //         mysig.PWR <= 0;
    //         mysig.VREF_CA <= 0;
    //         mysig.VREF_DQ <= 0;
    //         mysig.ADDR <= 0;
    //         mysig.ADDR_17 <= 0;
    //         mysig.C <= 0;
    //         mysig.BG <= 0;
    //         mysig.BA <= 0;
    //     end else begin
    //         mysig.ACT_n <= nACT_n;
    //         mysig.RAS_n_A16 <= nRAS_n_A16;
    //         mysig.CAS_n_A15 <= nCAS_n_A15;
    //         mysig.WE_n_A14 <= nWE_n_A14;
    //         mysig.ALERT_n <= nALERT_n;
    //         mysig.PARITY <= nPARITY;
    //         mysig.RESET_n <= nRESET_n;
    //         mysig.TEN <= nTEN;
    //         mysig.CS_n <= nCS_n;
    //         mysig.CKE <= nCKE;
    //         mysig.ODT <= nODT;
    //         mysig.ZQ <= nZQ;
    //         mysig.PWR <= nPWR;
    //         mysig.VREF_CA <= nVREF_CA;
    //         mysig.VREF_DQ <= nVREF_DQ;
    //         mysig.C <= nC;
    //         mysig.BG <= mysig.BG;
    //         mysig.BA <= mysig.BA;
    //         mysig.ADDR <= mysig.ADDR;
    //         mysig.ADDR_17 <= mysig.ADDR_17;
    //     end
    // end


    always_comb begin : OUTPUT_VALUE
        // Default values
        cmd_addr   = DESEL_CMD;
        mysig.ALERT_n   = 1'b1;
        mysig.PARITY    = 1'b0;
        mysig.RESET_n   = 1'b1;
        mysig.TEN       = 1'b0;
        mysig.ODT       = 1'b0;
        mysig.C         = '0;
        mysig.BG        = '0;
        mysig.BA        = '0;
        mysig.ADDR      = '0;
        mysig.CKE       = 1'b1;
        mysig.ADDR_17   = 1'b0;

        mysig.ZQ        = 1'b0;
        mysig.PWR       = 1'b1;
        mysig.VREF_CA   = 1'b1;
        mysig.VREF_DQ   = 1'b1;

        // pass-through by default
        // mysig.ACT_n     = mysig.ACT_n;
        // mysig.RAS_n_A16 = mysig.RAS_n_A16;
        // mysig.CAS_n_A15 = mysig.CAS_n_A15;
        // mysig.WE_n_A14  = mysig.WE_n_A14;
        // mysig.CS_n      = mysig.CS_n;

    case (mysig.state)
        POWER_UP: begin
            cmd_addr = POWER_UP_PRG;
            mysig.CKE     = 1'b0;
            mysig.TEN     = 1'b0;
            mysig.RESET_n = 1'b0;
            mysig.PWR     = 1'b0;
            mysig.VREF_CA = 1'b0;
            mysig.VREF_DQ = 1'b0;
        end

        PRE_RESET: begin
            cmd_addr = POWER_UP_PRG;
            mysig.CKE     = 1'b0;
            mysig.TEN     = 1'b0;
            mysig.RESET_n = 1'b0;
            mysig.PWR     = 1'b1;
            mysig.VREF_CA = 1'b1;
            mysig.VREF_DQ = 1'b1;
        end

        RESET: begin
            cmd_addr = POWER_UP_PRG;
            mysig.CKE     = 1'b0;
            mysig.TEN     = 1'b0;
            mysig.RESET_n = 1'b1;
        end

        NOP: begin
            cmd_addr = DESEL_CMD;
        end

        LOAD_MODE_DLL: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h0;
                mysig.BA      = 2'h1;
                mysig.ADDR    = 14'h1;
            end
        end

        LOAD_BG0_REG3: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h0;
                mysig.BA      = 2'h3;
                mysig.ADDR    = 14'h0;
            end
        end

        LOAD_BG1_REG6: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h1;
                mysig.BA      = 2'h2;
                mysig.ADDR    = 14'h080F;
            end
        end

        LOAD_BG1_REG5: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h1;
                mysig.BA      = 2'h1;
                mysig.ADDR     = 14'h1000;
            end
        end

        LOAD_BG1_REG4: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h1;
                mysig.BA      = 2'h0;
                mysig.ADDR    = 14'h1000;
            end
        end

        LOAD_BG0_REG2: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h0;
                mysig.BA      = 2'h2;
                mysig.ADDR    = 14'h0088;
            end
        end

        LOAD_BG0_REG1: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h0;
                mysig.BA      = 2'h1;
                mysig.ADDR    = 14'h0000;
                //A[0] for DLL disable
                // dr_ram.ADDR     = 14'h0001;
            end
        end

        LOAD_BG0_REG0: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                mysig.BG      = 2'h0;
                mysig.BA      = 2'h0;
                mysig.ADDR    = 14'h041d;
            end
        end

        ZQ_CL: begin
            if (issue) begin
                cmd_addr = ZQ_CMD;
                mysig.ADDR    = 14'h0400;
            end
        end

        ACTIVATE: begin
            if (issue) begin
                // cmd_addr = cmd_t'({2'b0, mysig.R0[16], mysig.R0[15], mysig.R0[14]});
                cmd_addr = cmd_t'({2'b0, 1'b0, 1'b0, mysig.R0[14]});
                mysig.BG      = mysig.BG0;
                mysig.BA      = mysig.BA0;
                mysig.ADDR    = mysig.R0[13:0];
            end
        end

        WRITE: begin
            if (issue) begin
                cmd_addr   = WRITE_CMD;
                mysig.BG        = mysig.BG0;
                mysig.BA        = mysig.BA0;
                mysig.RAS_n_A16 = 1'b1;
                mysig.CAS_n_A15 = 1'b0;
                mysig.WE_n_A14  = 1'b0;
                mysig.ADDR      = {1'b0, 1'b1, 1'b0, 1'b0, mysig.C0};
            end
        end

        READ: begin
            if (issue) begin
                cmd_addr   = READ_CMD;
                mysig.BG        = mysig.BG0;
                mysig.BA        = mysig.BA0;
                mysig.ADDR      = {1'b0, 1'b1, 1'b0, 1'b0, mysig.C0};
            end
        end

        PRECHARGE: begin
            if (issue) begin
                cmd_addr    = PRECHARGE_CMD;
                mysig.BG         = mysig.BG0;
                mysig.BA         = mysig.BA0;
                mysig.ADDR[10]   = mysig.ref_re ? 1'b1 : 1'b0;
            end
        end

        REFRESH: begin
            if (issue) begin
                cmd_addr = REFRESH_CMD;
                mysig.BG =0;
                mysig.BA = 0;
            end
        end

        default: begin
            cmd_addr = DESEL_CMD;
        end
    endcase

    //Assign cmd into DRAM interface
    {mysig.CS_n, mysig.ACT_n, mysig.RAS_n_A16, mysig.CAS_n_A15, mysig.WE_n_A14} = cmd_addr;
end

endmodule