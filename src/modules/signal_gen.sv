`timescale 1ns/1ps
`include "signal_gen_if.vh"
`include "control_unit_if.vh"
`include "dram_pkg.vh"

module signal_gen #(

) (
    input logic CLK,
    input logic nRST,
    signal_gen_if.dram mysig,
    control_unit_if.sig_gen cuif
);
    import dram_pkg::*;

    logic [4:0] cmd_addr;
    logic issue;

    assign issue = (cuif.state != cuif.nstate);

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

    case (cuif.state)
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
                mysig.ADDR     = 14'b0001000_0000000;
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
                mysig.ADDR    = 14'h0001;
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
            if (issue && !cuif.rf_req) begin
                // cmd_addr = cmd_t'({2'b0, cuif.row[16], cuif.row[15], cuif.row[14]});
                cmd_addr = cmd_t'({2'b0, 1'b0, 1'b0, cuif.row[14]});
                mysig.BG      = cuif.BG;
                mysig.BA      = cuif.bank;
                mysig.ADDR    = cuif.row[13:0];
            end
        end

        WRITE: begin
            if (issue && !cuif.rf_req) begin
                cmd_addr   = WRITE_CMD;
                mysig.BG        = cuif.BG;
                mysig.BA        = cuif.bank;
                mysig.RAS_n_A16 = 1'b1;
                mysig.CAS_n_A15 = 1'b0;
                mysig.WE_n_A14  = 1'b0;
                mysig.ADDR      = {1'b0, 1'b1, 1'b0, 1'b0, cuif.col};
            end
        end

        READ: begin
            if (issue && !cuif.rf_req) begin
                cmd_addr   = READ_CMD;
                mysig.BG        = cuif.BG;
                mysig.BA        = cuif.bank;
                mysig.ADDR      = {1'b0, 1'b1, 1'b0, 1'b0, cuif.col};
            end
        end

        PRECHARGE: begin
            if (issue) begin
                cmd_addr    = PRECHARGE_CMD;
                mysig.BG         = cuif.BG;
                mysig.BA         = cuif.bank;
                mysig.ADDR[10]   = cuif.rf_req ? 1'b1 : 1'b0;
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