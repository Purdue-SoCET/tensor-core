`timescale 1ns/1ps
`include "signal_gen_if.vh"

module signal_gen #(

) (
    input logic CLK,
    input logic nRST,
    signal_gen_if.dut mysig,
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


    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            mysig.ACT_n          <= 0;
            mysig.RAS_n_A16 <= 0;
            mysig.CAS_n_A15 <= 0;
            mysig.WE_n_A14 <= 0;
            mysig.ALERT_n <= 0;
            mysig.PARITY <= 0;
            mysig.RESET_n <= 0;
            mysig.TEN         <= 0;
            mysig.CS_n <= 0;
            mysig.CKE <= 0;
            mysig.ODT <= 0;
            mysig.ZQ <= 0;
            mysig.PWR <= 0;
            mysig.VREF_CA <= 0;
            mysig.VREF_DQ <= 0;
            mysig.ADDR <= 0;
            mysig.ADDR_17 <= 0;
            mysig.C <= 0;
            mysig.BG <= 0;
            mysig.BA <= 0;
        end else begin
            mysig.ACT_n <= nACT_n;
            mysig.RAS_n_A16 <= nRAS_n_A16;
            mysig.CAS_n_A15 <= nCAS_n_A15;
            mysig.WE_n_A14 <= nWE_n_A14;
            mysig.ALERT_n <= ALERT_n;
            mysig.PARITY <= nPARITY;
            mysig.RESET_n <= nRESET_n;
            mysig.TEN <= nTEN;
            mysig.CS_n <= nCS_n;
            mysig.CKE <= nCKE;
            mysig.ODT <= nODT;
            mysig.ZQ <= nZQ;
            mysig.PWR <= nPWR;
            mysig.VREF_CA <= nVREF_CA;
            mysig.VREF_DQ <= nVREF_DQ;
            mysig.C <= nC;
            mysig.BG <= nBG;
            mysig.BA <= nBA;
            mysig.ADDR <= nADDR;
            mysig.ADDR_17 <= nADDR_17;
        end
    end


    always_comb begin : OUTPUT_VALUE
        // Default values
        cmd_addr   = DESEL_CMD;
        nALERT_n   = 1'b1;
        nPARITY    = 1'b0;
        nRESET_n   = 1'b1;
        nTEN       = 1'b0;
        nODT       = 1'b0;
        nC         = '0;
        nBG        = '0;
        nBA        = '0;
        nADDR      = '0;
        nCKE       = 1'b1;
        nADDR_17   = 1'b0;

        nZQ        = 1'b0;
        nPWR       = 1'b1;
        nVREF_CA   = 1'b1;
        nVREF_DQ   = 1'b1;

        // pass-through by default
        nACT_n     = ACT_n;
        nRAS_n_A16 = RAS_n_A16;
        nCAS_n_A15 = CAS_n_A15;
        nWE_n_A14  = WE_n_A14;
        nCS_n      = CS_n;

    case (state)
        POWER_UP: begin
            cmd_addr = POWER_UP_PRG;
            nCKE     = 1'b0;
            nTEN     = 1'b0;
            nRESET_n = 1'b0;
            nPWR     = 1'b0;
            nVREF_CA = 1'b0;
            nVREF_DQ = 1'b0;
        end

        PRE_RESET: begin
            cmd_addr = POWER_UP_PRG;
            nCKE     = 1'b0;
            nTEN     = 1'b0;
            nRESET_n = 1'b0;
            nPWR     = 1'b1;
            nVREF_CA = 1'b1;
            nVREF_DQ = 1'b1;
        end

        RESET: begin
            cmd_addr = POWER_UP_PRG;
            nCKE     = 1'b0;
            nTEN     = 1'b0;
            nRESET_n = 1'b1;
        end

        NOP: begin
            cmd_addr = DESEL_CMD;
        end

        LOAD_MODE_DLL: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h0;
                nBA      = 2'h1;
                nADDR    = 14'h1;
            end
        end

        LOAD_BG0_REG3: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h0;
                nBA      = 2'h3;
                nADDR    = 14'h0;
            end
        end

        LOAD_BG1_REG6: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h1;
                nBA      = 2'h2;
                nADDR    = 14'h080F;
            end
        end

        LOAD_BG1_REG5: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h1;
                nBA      = 2'h1;
                nADDR    = 14'h0;
            end
        end

        LOAD_BG1_REG4: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h1;
                nBA      = 2'h0;
                nADDR    = 14'h1000;
            end
        end

        LOAD_BG0_REG2: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h0;
                nBA      = 2'h2;
                nADDR    = 14'h0088;
            end
        end

        LOAD_BG0_REG1: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h0;
                nBA      = 2'h1;
                nADDR    = 14'h0001;
            end
        end

        LOAD_BG0_REG0: begin
            if (issue) begin
                cmd_addr = LOAD_MODE_CMD;
                nBG      = 2'h0;
                nBA      = 2'h0;
                nADDR    = 14'h041d;
            end
        end

        ZQ_CL: begin
            if (issue) begin
                cmd_addr = ZQ_CMD;
                nADDR    = 14'h0400;
            end
        end

        ACTIVATE: begin
            if (issue) begin
                cmd_addr = cmd_t'({2'b0, mysig.R0[16], mysig.R0[15], mysig.R0[14]});
                nBG      = mysig.BG0;
                nBA      = mysig.BA0;
                nADDR    = mysig.R0[13:0];
            end
        end

        WRITE: begin
            if (issue) begin
                cmd_addr   = WRITE_CMD;
                nBG        = mysig.BG0;
                nBA        = mysig.BA0;
                nRAS_n_A16 = 1'b1;
                nCAS_n_A15 = 1'b0;
                nWE_n_A14  = 1'b0;
                nADDR      = {1'b0, 1'b1, 1'b0, 1'b0, mysig.COL0};
            end
        end

        READ: begin
            if (issue) begin
                cmd_addr   = READ_CMD;
                nBG        = mysig.BG0;
                nBA        = mysig.BA0;
                nADDR      = {1'b0, 1'b1, 1'b0, 1'b0, mysig.COL0};
            end
        end

        PRECHARGE: begin
            if (issue) begin
                cmd_addr    = PRECHARGE_CMD;
                nBG         = mysig.BG0;
                nBA         = mysig.BA0;
                nADDR[10]   = 1'b0;
            end
        end


        //REFRESH

        default: begin
            cmd_addr = DESEL_CMD;
        end
    endcase

    //Assign cmd into DRAM interface
    {nCS_n, nACT_n, nRAS_n_A16, nCAS_n_A15, nWE_n_A14} = cmd_addr;
end

endmodule