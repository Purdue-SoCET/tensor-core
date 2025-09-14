`include "dram_command_if.vh"
`include "scheduler_buffer_if.vh"
`include "data_transfer_if.vh"
`include "arch_defines.v"
//`include "StateTable.svp"
`timescale 1 ns / 1 ps

module dram_command_tb;
    parameter PERIOD = 1.25;
    parameter tCK = 1.25;
    import dram_pack::*;
    // signals
    logic CLK, CLKx2;
    reg model_enable_val;
    string task_name;

    addr_x4_t ramaddr_phy, ramaddr_phy_ft, ramstore_phy, ramstore_phy_ft;
    reg clk_val, clk_enb;
    // DQ transmit
    reg dq_en;
    reg dqs_en;
    reg[MAX_DQ_BITS-1:0] dq_out;
    reg[MAX_DQS_BITS-1:0] dqs_out;
    reg[MAX_DM_BITS-1:0] dm_out;

    always begin
        CLK = 1'b0;
        #(CLK_PERIOD / 2.0);
        CLK = 1'b1;
        #(CLK_PERIOD / 2.0);
    end

    always begin
        CLKx2 = 1'b1;
        #(CLK_PERIOD / 4.0);
        CLKx2 = 1'b0;
        #(CLK_PERIOD / 4.0);
    end

    dram_command_if dc_if();
    scheduler_buffer_if sch_if();
    data_transfer_if dt_if();
    

    dram_command DUT (.CLK(CLK), .nRST(nRST), .dr_ram(dc_if), .dr_sche(dc_if));
    scheduler_buffer SCH_BUFF (.CLK(CLK), .nRST(nRST), .mysche(sch_if));
    data_transfer DT (.CLK(CLK), .nRST(nRST), .mydata(dt_if));

    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4();

    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS), .CONFIGURED_RANKS(CONFIGURED_RANKS))
                 golden_model(.model_enable(model_enable), .iDDR4(iDDR4));


    //Interface between iDDR4 and data transfer
    assign iDDR4.DQ = dq_en ?     dt_if.DQ : {MAX_DQ_BITS{1'bz}};
    assign iDDR4.DQS_t = dq_en ? dt_if.DQS_t : {MAX_DQS_BITS{1'bz}};
    assign iDDR4.DQS_c = dq_en ? dt_if.DQS_c : {MAX_DQS_BITS{1'bz}};

    assign dt_if.DQ = ~dq_en ? iDDR4.DQ : {MAX_DQ_BITS{1'bz}};
    assign dt_if.DQS_t = ~dq_en ? iDDR4.DQS_t : {MAX_DQS_BITS{1'bz}};
    assign dt_if.DQS_c = ~dq_en ? iDDR4.DQS_c : {MAX_DQS_BITS{1'bz}};


    always_comb begin
      //Interface of schduler buffer
      ramaddr_phy = addr_x4_t'(sch_if.ramaddr_rq);
      ramaddr_phy_ft = addr_x4_t'(sch_if.ramaddr_rq_ft);
      dc_if.Ra0 = {'0, ramaddr_phy.rank};
      dc_if.Ra1 = {'0, ramaddr_phy_ft.rank};
      dc_if.BA0 = {'0, ramaddr_phy.bank};
      dc_if.BA1 =  {'0, ramaddr_phy_ft.bank};
      dc_if.R0 = {'0, ramaddr_phy.row};
      dc_if.R1 = {'0, ramaddr_phy_ft.row};
      dc_if.COL0 = {'0, ramaddr_phy.col_1, ramaddr_phy.col_0};
      // dc_if.COL0 = {'0, ramaddr_phy.col_1, 3'b10};
      dc_if.COL1  = {'0, ramaddr_phy_ft.col_1, ramaddr_phy_ft.col_0};
      dc_if.BG0   = {'0, ramaddr_phy.bg1, ramaddr_phy.bg0};
      dc_if.BG1   = {'0, ramaddr_phy_ft.bg1, ramaddr_phy_ft.bg0};

      dc_if.ramREN_curr = sch_if.ramREN_curr;
      dc_if.ramREN_ftrt = sch_if.ramREN_ftrt;
      dc_if.ramWEN_curr = sch_if.ramWEN_curr;
      dc_if.ramWEN_ftrt = sch_if.ramWEN_ftrt;
      sch_if.request_done = dc_if.request_done;
      

      //Interface between dram command and the data_transfer

      dt_if.wr_en = dc_if.wr_en;
      dt_if.rd_en = dc_if.rd_en;
      

      // scheduler buffer -> Data_transfer
      //dt_if.memstore = sch_if.ramstore_rq;
      


    end

    //Interface between dram command and ddr4
    // assign iDDR4.DM_n = dq_en ? dm_out : {MAX_DM_BITS{1'bz}};
    // assign iDDR4.DQ = dq_en ? dq_out : {MAX_DQ_BITS{1'bz}};
    // assign iDDR4.DQS_t = dqs_en ? dqs_out : {MAX_DQS_BITS{1'bz}};
    // assign iDDR4.DQS_c = dqs_en ? ~dqs_out : {MAX_DQS_BITS{1'bz}};
    assign model_enable = model_enable_val;

    initial begin
      iDDR4.CK <= 2'b01;
      clk_enb <= 1'b1;
      clk_val <= 1'b1;  
      model_enable_val = 1;
      dc_if.REFRESH = 1'b0;

      dq_en = 1'b1;

      nRST = 1'b0;
      @(posedge CLK);
      @(posedge CLK);
      nRST = 1'b1;
      task_name = "Power_up";
      // repeat (2254) @(posedge CLK);
      #((tRESET + tPWUP + tRESETCKE + tPDc + tXPR + tDLLKc + tMOD * 7 + tZQinitc) * PERIOD);



      //Add request
      //add_request(.addr(32'hAAAA_BBBB), .write(1'b1), .data(32'hDDCC_BBAA));
      add_request(.addr({'0, 3'd2,2'b00}), .write(1'b1), .data(32'hDDCC_BBAA));
      repeat (200) @(posedge CLK);

      task_name = "Add Read";
      add_request(.addr({'0, 3'd2,2'b00}), .write(1'b0), .data(32'hDDCC_BBAA));
      dq_en = 1'b0;
      task_name = "Done add Read";
      repeat (200) @(posedge CLK);

      
      task_name = "After 400 cycle Read";
      // #(10000);
      $finish;

    end

    task add_request(input logic [31:0] addr, input logic write, input logic [31:0] data);
      if (write) begin
          sch_if.dWEN = 1'b1;
          sch_if.dREN = 1'b0;
          sch_if.ramaddr = addr;
          sch_if.memstore = data;
      end else begin
          sch_if.dWEN = 1'b0;
          sch_if.dREN = 1'b1;
          sch_if.ramaddr = addr;
      end
      #(PERIOD);
      // @(posedge CLK);
      sch_if.dWEN = 1'b0;
      sch_if.dREN = 1'b0;
    endtask
    
    
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