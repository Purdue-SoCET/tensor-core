`include "dram_command_if.vh"
`include "scheduler_buffer_if.vh"
`include "data_transfer_if.vh"
`include "arch_defines.v"
`include "dimm.vh"

`timescale 1 ns / 1 ps

module dram_cmd_dimm_tb;
    parameter PERIOD = 1.5;
    parameter tCK = 1.5;
    import dram_pack::*;
    // import arch_package::*;
    import proj_package::*;
    
    // signals
    logic CLK = 1, nRST;
    logic CLKx2=0;
    reg model_enable_val;
    string task_name;

    //Instantiate the the iDDR4_1 version
    
    addr_x4_t ramaddr_phy, ramaddr_phy_ft, ramstore_phy, ramstore_phy_ft;
    reg clk_val, clk_enb;
    // DQ transmit
    reg dq_en;
    reg dqs_en;
    reg[MAX_DQ_BITS-1:0] dq_out;
    reg[MAX_DQS_BITS-1:0] dqs_out;
    reg[MAX_DM_BITS-1:0] dm_out;
    logic [31:0] data_store1;
    logic [31:0] data_store2;
    logic [31:0] data_store3;
    logic [31:0] data_store4;
    logic DM_debug;
    assign model_enable = model_enable_val;
    // always #(PERIOD/2) CLK++;
    // always #(PERIOD/4) CLKx2++;

    always begin
        CLK = 1'b0;
        #(PERIOD / 2.0);
        CLK = 1'b1;
        #(PERIOD / 2.0);
    end

    always begin
        CLKx2 = 1'b1;
        #(PERIOD / 4.0);
        CLKx2 = 1'b0;
        #(PERIOD / 4.0);
    end

    // ddr4_module_if iDDR4_1();
    dram_command_if dc_if();
    scheduler_buffer_if sch_if();
    data_transfer_if dt_if();
    
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_1();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_2();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_3();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_4();


    dram_command DUT (.CLK(CLK), .nRST(nRST), .dr_ram(dc_if), .dr_sche(dc_if));
    scheduler_buffer SCH_BUFF (.CLK(CLK), .nRST(nRST), .mysche(sch_if));
    data_transfer DT (.CLK(CLK), .CLKx2(CLKx2),.nRST(nRST), .mydata(dt_if));

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
      //dt_if.memstore = sch_if.ramstore_rq;
    end

    always @(posedge clk_val && clk_enb) begin
        clk_val <= #(tCK/2) 1'b0;
        clk_val <= #(tCK) 1'b1;
        iDDR4_1.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_1.CK[1] <= #(tCK) 1'b1;
        iDDR4_1.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_1.CK[0] <= #(tCK) 1'b0;
        iDDR4_1.ACT_n     <= dc_if.ACT_n;
        iDDR4_1.RAS_n_A16 <= dc_if.RAS_n_A16;
        iDDR4_1.CAS_n_A15 <= dc_if.CAS_n_A15;
        iDDR4_1.WE_n_A14  <= dc_if.WE_n_A14;
        iDDR4_1.ALERT_n   <= dc_if.ALERT_n;
        iDDR4_1.PARITY    <= dc_if.PARITY;
        iDDR4_1.RESET_n   <= dc_if.RESET_n;
        iDDR4_1.TEN       <= dc_if.TEN;
        iDDR4_1.CS_n      <= dc_if.CS_n;
        iDDR4_1.CKE       <= dc_if.CKE;
        iDDR4_1.ODT       <= dc_if.ODT;
        iDDR4_1.C         <= dc_if.C;
        iDDR4_1.BG        <= dc_if.BG;
        iDDR4_1.BA        <= dc_if.BA;
        iDDR4_1.ADDR      <= dc_if.ADDR;
        iDDR4_1.ADDR_17   <= dc_if.ADDR_17;
        iDDR4_1.ZQ <= dc_if.ZQ;
        iDDR4_1.PWR <= dc_if.PWR;
        iDDR4_1.VREF_CA <= dc_if.VREF_CA;
        iDDR4_1.VREF_DQ <= dc_if.VREF_DQ;
    end

    always @(posedge clk_val && clk_enb) begin
        iDDR4_2.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_2.CK[1] <= #(tCK) 1'b1;
        iDDR4_2.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_2.CK[0] <= #(tCK) 1'b0;
        iDDR4_2.ACT_n     <= dc_if.ACT_n;
        iDDR4_2.RAS_n_A16 <= dc_if.RAS_n_A16;
        iDDR4_2.CAS_n_A15 <= dc_if.CAS_n_A15;
        iDDR4_2.WE_n_A14  <= dc_if.WE_n_A14;
        iDDR4_2.ALERT_n   <= dc_if.ALERT_n;
        iDDR4_2.PARITY    <= dc_if.PARITY;
        iDDR4_2.RESET_n   <= dc_if.RESET_n;
        iDDR4_2.TEN       <= dc_if.TEN;
        iDDR4_2.CS_n      <= dc_if.CS_n;
        iDDR4_2.CKE       <= dc_if.CKE;
        iDDR4_2.ODT       <= dc_if.ODT;
        iDDR4_2.C         <= dc_if.C;
        iDDR4_2.BG        <= dc_if.BG;
        iDDR4_2.BA        <= dc_if.BA;
        iDDR4_2.ADDR      <= dc_if.ADDR;
        iDDR4_2.ADDR_17   <= dc_if.ADDR_17;
        iDDR4_2.ZQ        <= dc_if.ZQ;
        iDDR4_2.PWR       <= dc_if.PWR;
        iDDR4_2.VREF_CA   <= dc_if.VREF_CA;
        iDDR4_2.VREF_DQ   <= dc_if.VREF_DQ;
    end

    always @(posedge clk_val && clk_enb) begin
        iDDR4_3.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_3.CK[1] <= #(tCK) 1'b1;
        iDDR4_3.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_3.CK[0] <= #(tCK) 1'b0;
        iDDR4_3.ACT_n     <= dc_if.ACT_n;
        iDDR4_3.RAS_n_A16 <= dc_if.RAS_n_A16;
        iDDR4_3.CAS_n_A15 <= dc_if.CAS_n_A15;
        iDDR4_3.WE_n_A14  <= dc_if.WE_n_A14;
        iDDR4_3.ALERT_n   <= dc_if.ALERT_n;
        iDDR4_3.PARITY    <= dc_if.PARITY;
        iDDR4_3.RESET_n   <= dc_if.RESET_n;
        iDDR4_3.TEN       <= dc_if.TEN;
        iDDR4_3.CS_n      <= dc_if.CS_n;
        iDDR4_3.CKE       <= dc_if.CKE;
        iDDR4_3.ODT       <= dc_if.ODT;
        iDDR4_3.C         <= dc_if.C;
        iDDR4_3.BG        <= dc_if.BG;
        iDDR4_3.BA        <= dc_if.BA;
        iDDR4_3.ADDR      <= dc_if.ADDR;
        iDDR4_3.ADDR_17   <= dc_if.ADDR_17;
        iDDR4_3.ZQ <= dc_if.ZQ;
        iDDR4_3.PWR <= dc_if.PWR;
        iDDR4_3.VREF_CA <= dc_if.VREF_CA;
        iDDR4_3.VREF_DQ <= dc_if.VREF_DQ;
    end

    always @(posedge clk_val && clk_enb) begin
        iDDR4_4.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_4.CK[1] <= #(tCK) 1'b1;
        iDDR4_4.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_4.CK[0] <= #(tCK) 1'b0;
        iDDR4_4.ACT_n     <= dc_if.ACT_n;
        iDDR4_4.RAS_n_A16 <= dc_if.RAS_n_A16;
        iDDR4_4.CAS_n_A15 <= dc_if.CAS_n_A15;
        iDDR4_4.WE_n_A14  <= dc_if.WE_n_A14;
        iDDR4_4.ALERT_n   <= dc_if.ALERT_n;
        iDDR4_4.PARITY    <= dc_if.PARITY;
        iDDR4_4.RESET_n   <= dc_if.RESET_n;
        iDDR4_4.TEN       <= dc_if.TEN;
        iDDR4_4.CS_n      <= dc_if.CS_n;
        iDDR4_4.CKE       <= dc_if.CKE;
        iDDR4_4.ODT       <= dc_if.ODT;
        iDDR4_4.C         <= dc_if.C;
        iDDR4_4.BG        <= dc_if.BG;
        iDDR4_4.BA        <= dc_if.BA;
        iDDR4_4.ADDR      <= dc_if.ADDR;
        iDDR4_4.ADDR_17   <= dc_if.ADDR_17;
        iDDR4_4.ZQ <= dc_if.ZQ;
        iDDR4_4.PWR <= dc_if.PWR;
        iDDR4_4.VREF_CA <= dc_if.VREF_CA;
        iDDR4_4.VREF_DQ <= dc_if.VREF_DQ;
    end


    //Interface between iDDR4 and data transfer example
    // assign iDDR4.DQ = dq_en ?     dt_if.DQ : {MAX_DQ_BITS{1'bz}};
    // assign iDDR4.DQS_t = dq_en ? dt_if.DQS_t : {MAX_DQS_BITS{1'bz}};
    // assign iDDR4.DQS_c = dq_en ? dt_if.DQS_c : {MAX_DQS_BITS{1'bz}};
    // assign dt_if.DQ = ~dq_en ? iDDR4.DQ : {MAX_DQ_BITS{1'bz}};
    // assign dt_if.DQS_t = ~dq_en ? iDDR4.DQS_t : {MAX_DQS_BITS{1'bz}};
    // assign dt_if.DQS_c = ~dq_en ? iDDR4.DQS_c : {MAX_DQS_BITS{1'bz}};

    // Component instantiation
    //Only use 4 chips only
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u0_r0(.model_enable(model_enable), .iDDR4(iDDR4_1));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u1_r0(.model_enable(model_enable), .iDDR4(iDDR4_2));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u2_r0(.model_enable(model_enable), .iDDR4(iDDR4_3));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u3_r0(.model_enable(model_enable), .iDDR4(iDDR4_4));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u4_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u4_r0));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u5_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u5_r0));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u6_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u6_r0));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u7_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u7_r0));
    assign {
        iDDR4_1.DQ,
        iDDR4_2.DQ,
        iDDR4_3.DQ,
        iDDR4_4.DQ
    } = dq_en ? {dt_if.DQ} : {32{1'bz}};


    assign {
        iDDR4_1.DQS_t,
        iDDR4_2.DQS_t,
        iDDR4_3.DQS_t,
        iDDR4_4.DQS_t
    } = dq_en ? {dt_if.DQS_t,
                 dt_if.DQS_t,
                 dt_if.DQS_t,
                 dt_if.DQS_t  
                 } : 4'bzz;

    assign {
        iDDR4_1.DQS_c,
        iDDR4_2.DQS_c,
        iDDR4_3.DQS_c,
        iDDR4_4.DQS_c
    } = dq_en ? {
        dt_if.DQS_c,
        dt_if.DQS_c,
        dt_if.DQS_c,
        dt_if.DQS_c
        } : 4'bzz;

    // assign {
    //     iDDR4_1.DM_n,
    //     iDDR4_2.DM_n,
    //     iDDR4_3.DM_n,
    //     iDDR4_4.DM_n
    // } = dq_en ? {
    //     dt_if.DM_n,
    //     dt_if.DM_n,
    //     dt_if.DM_n,
    //     dt_if.DM_n
    // } : 4'bzz;

    assign {
        iDDR4_1.DM_n,
        iDDR4_2.DM_n,
        iDDR4_3.DM_n,
        iDDR4_4.DM_n
    } = dq_en ? {
        DM_debug,
        DM_debug,
        DM_debug,
        DM_debug
    } : 4'bzz;



    assign dt_if.DQ = ~dq_en ? {
        iDDR4_1.DQ,
        iDDR4_2.DQ,
        iDDR4_3.DQ,
        iDDR4_4.DQ
    } : {32{1'bz}};


    assign dt_if.DQS_t = ~dq_en ? iDDR4_1.DQS_t : 1'bz;
    assign dt_if.DQS_c = ~dq_en ? iDDR4_1.DQS_c: 1'bz;
    assign dt_if.DM_n = ~dq_en ? iDDR4_1.DM_n: 1'bz;
    assign dt_if.COL_choice = ramaddr_phy.col_0;


    task writing_1();
        task_name = "Write 1";
        DM_debug = 1'b1;
        add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b1), .data(32'hAAAA_AAAA));
        data_store1 = 32'h1111_1111;
        data_store2 = 32'h2222_2222;
        data_store3 = 32'h3333_3333;
        data_store4 = 32'h4444_4444;
        
        while (!dt_if.wr_en) begin
            @(posedge CLK);
        end
        dt_if.memstore = data_store1;
        @(posedge CLKx2);
        dt_if.memstore = data_store1;
        @(posedge CLKx2);
        dt_if.memstore = data_store2;
        @(posedge CLKx2);
        dt_if.memstore = data_store3;
        @(posedge CLKx2);
        dt_if.memstore = data_store4;
        @(posedge CLKx2);
        dt_if.memstore = 32'h5555_5555;
        @(posedge CLKx2);
        dt_if.memstore = 32'h6666_6666;
        @(posedge CLKx2);
        dt_if.memstore = 32'h7777_7777;
        @(posedge CLKx2);
        dt_if.memstore = 32'h8888_8888;
        @(posedge CLK);
        
        dt_if.clear = 1'b1;
        
        @(posedge CLK);
        dt_if.clear = 1'b0;

    endtask

    task writing_2();
        
        task_name = "Write 2";
        DM_debug = 1'b0;
        add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b1), .data(32'hAAAA_AAAA));
        data_store1 = 32'hAAAA_AAAA;
        data_store2 = 32'hBBBB_BBBB;
        data_store3 = 32'hCCCC_CCCC;
        data_store4 = 32'hDDDD_DDDD;
        
        while (!dt_if.wr_en) begin
            @(posedge CLK);
        end
        dt_if.memstore = data_store1;
        @(posedge CLKx2);
        dt_if.memstore = data_store1;
        @(posedge CLKx2);
        dt_if.memstore = data_store2;
        @(posedge CLKx2);
        dt_if.memstore = data_store3;
        @(posedge CLKx2);
        dt_if.memstore = data_store4;
        @(posedge CLKx2);
        dt_if.memstore = 32'hAABB_5555;
        @(posedge CLKx2);
        dt_if.memstore = 32'hAABB_6666;
        @(posedge CLKx2);
        dt_if.memstore = 32'hAABB_7777;
        @(posedge CLKx2);
        dt_if.memstore = 32'hAABB_8888;
        @(posedge CLK);
        
        dt_if.clear = 1'b1;
        
        @(posedge CLK);
        dt_if.clear = 1'b0;
    endtask

    task read_chk();
        DM_debug = 1'bzz;
        task_name = "Add Read";
        add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b0), .data(32'hDDCC_BBAA));
        //   add_request(.addr({'0, 3'd1,2'b00}), .write(1'b0), .data(32'hDDCC_BBAA));
        dq_en = 1'b0;
        //   task_name = "Done add Read";
        //   repeat (200) @(posedge CLK);
        //   task_name = "After 400 cycle Read";
        repeat (100) @(posedge CLK);
    endtask

    initial begin
      iDDR4_1.CK <= 2'b01;
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

      writing_1();
      read_chk();
      dq_en = 1'b1;
      writing_2();
      read_chk();
      //Add request
      //Ignore the writing data
      
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_001_00}), .write(1'b1), .data(32'hBBBB_BBBB));
    //   repeat (100) @(posedge CLK);
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_010_00}), .write(1'b1), .data(32'hCCCC_CCCC));
    //   repeat (100) @(posedge CLK);
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_011_00}), .write(1'b1), .data(32'hDDDD_DDDD));
    //   repeat (100) @(posedge CLK);
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_100_00}), .write(1'b1), .data(32'hEEEE_EEEE));
    //   repeat (100) @(posedge CLK);
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_101_00}), .write(1'b1), .data(32'h1111_1111));
    //   repeat (100) @(posedge CLK);
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_110_00}), .write(1'b1), .data(32'h2222_2222));
    //   repeat (100) @(posedge CLK);
    //   add_request(.addr({16'hAAAA, 8'hAA, 8'b000_111_00}), .write(1'b1), .data(32'h3333_3333));
    //   add_request(.addr({'0, 3'd2,2'b00}), .write(1'b1), .data(32'hDDCC_BBAA));
      //repeat (100) @(posedge CLK);

      
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



endmodule