`include "dram_command_if.vh"
//`include "arch_defines.v"
//`include "StateTable.svp"
`timescale 1 ns / 1 ps

module dram_command_tb;
    parameter PERIOD = 1.25;
    parameter tCK = 1.25;
    import dram_pack::*;
    // signals
    logic CLK = 1, nRST;
    reg model_enable_val;
    always #(PERIOD/2) CLK++;

    dram_command_if dc_if();

    dram_command DUT (.CLK(CLK), .nRST(nRST), .dr_ram(dc_if), .dr_sche(dc_if));
    DDR4_if #(.CONFIGURED_DQ_BITS(16)) iDDR4();

    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_RANKS(CONFIGURED_RANKS))
                 golden_model(.model_enable(model_enable), .iDDR4(iDDR4));

    //Interface between dram command and ddr4
    

    

    reg clk_val, clk_enb;
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

    initial begin
      iDDR4.CK <= 2'b01;
      clk_enb <= 1'b1;
      clk_val <= 1'b1;  
      model_enable_val = 1;

      nRST = 1'b0;
      @(posedge CLK);
      @(posedge CLK);
      nRST = 1'b1;
      repeat (300) @(posedge CLK);

      #(10000);
      $finish;

    end

    always @(posedge clk_val && clk_enb) begin
      clk_val <= #(tCK/2) 1'b0;
      clk_val <= #(tCK) 1'b1;
      iDDR4.CK[1] <= #(tCK/2) 1'b0;
      iDDR4.CK[1] <= #(tCK) 1'b1;
      iDDR4.CK[0] <= #(tCK/2) 1'b1;
      iDDR4.CK[0] <= #(tCK) 1'b0;
    end
    always @(posedge clk_val && clk_enb) begin
       iDDR4.ACT_n     <= dc_if.ACT_n;
      iDDR4.RAS_n_A16 <= dc_if.RAS_n_A16;
      iDDR4.CAS_n_A15 <= dc_if.CAS_n_A15;
      iDDR4.WE_n_A14  <= dc_if.WE_n_A14;
      iDDR4.ALERT_n   <= dc_if.ALERT_n;
      iDDR4.PARITY    <= dc_if.PARITY;
      iDDR4.RESET_n   <= dc_if.RESET_n;
      iDDR4.TEN       <= dc_if.TEN;
      iDDR4.CS_n      <= dc_if.CS_n;
      iDDR4.CKE       <= dc_if.CKE;
      iDDR4.ODT       <= dc_if.ODT;
      iDDR4.C         <= dc_if.C;
      iDDR4.BG        <= dc_if.BG;
      iDDR4.BA        <= dc_if.BA;
      iDDR4.ADDR      <= dc_if.ADDR;
      iDDR4.ADDR_17   <= dc_if.ADDR_17;
      iDDR4.ZQ <= dc_if.ZQ;
      iDDR4.PWR <= dc_if.PWR;
      iDDR4.VREF_CA <= dc_if.VREF_CA;
      iDDR4.VREF_DQ <= dc_if.VREF_DQ;
    end

endmodule