`include "dram_pkg.vh"
`include "scheduler_buffer_if.vh"
`include "data_transfer_if.vh"
`include "control_unit_if.vh"
`include "signal_gen_if.vh"
`include "arch_defines.v"
`include "dimm.vh"
`timescale 1 ns / 1 ps

module dram_top_tb;
    parameter PERIOD = 1.5;
    parameter tCK = 1.5;
    import dram_pkg::*;
    // import arch_package::*;
    import proj_package::*;

    //parameter from dram_command_if.vh
    parameter int MAX_DQ_BITS         = 16;
    parameter int MAX_DQS_BITS        = 2;
    parameter int MAX_DM_BITS         = 2;
    parameter CONFIGURED_DQ_BITS     = 8;
    parameter CONFIGURED_DQS_BITS     = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_DM_BITS     = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_RANKS = 1;
    
    // signals
    logic CLK = 1, nRST;
    logic CLKx2=0;
    reg model_enable_val;
    string task_name;

    //Instantiate the the iDDR4_1 version
    // addr_x4_t ramaddr_phy, ramaddr_phy_ft, ramstore_phy, ramstore_phy_ft;
    reg clk_val, clk_enb;
    // DQ transmit
    reg[MAX_DQ_BITS-1:0] dq_out;
    reg[MAX_DQS_BITS-1:0] dqs_out;
    reg[MAX_DM_BITS-1:0] dm_out;
    logic [31:0] data_store1;
    logic [31:0] data_store2;
    logic [31:0] data_store3;
    logic [31:0] data_store4;
    logic DM_debug;
    assign model_enable = model_enable_val;

    //Signal flag to choose write or read
    reg dq_en;
    reg dqs_en;
    

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
    control_unit_if dc_if();
    signal_gen_if sig_if();
    scheduler_buffer_if sch_if();
    data_transfer_if dt_if();
    
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_1();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_2();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_3();
    DDR4_if #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS)) iDDR4_4();


    dram_top DUT (.CLK(CLK), .nRST(nRST), .myctrl(dc_if), .myctrl_sig(dc_if), .mysig(sig_if));
    scheduler_buffer SCH_BUFF (.CLK(CLK), .nRST(nRST), .mysche(sch_if));
    data_transfer DT (.CLK(CLK), .CLKx2(CLKx2),.nRST(nRST), .mydata(dt_if));

    //Scheduler interface with the 
    always_comb begin
      dc_if.dREN = (!dc_if.ram_wait) ? 0 : sch_if.ramREN_curr;
      dc_if.dWEN = (!dc_if.ram_wait) ? 0 : sch_if.ramWEN_curr;
      dc_if.ram_addr = sch_if.ramaddr_rq;
      
    //   dc_if.ramWEN_ftrt = sch_if.ramWEN_ftrt;
      sch_if.request_done = !dc_if.ram_wait;
    

      //Interface between dram command and the data_transfer
      dt_if.wr_en = dc_if.wr_en;
      dt_if.rd_en = dc_if.rd_en;
      dt_if.memstore = sch_if.ramstore_rq;
    end

    always @(posedge clk_val && clk_enb) begin
        clk_val <= #(tCK/2) 1'b0;
        clk_val <= #(tCK) 1'b1;
        iDDR4_1.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_1.CK[1] <= #(tCK) 1'b1;
        iDDR4_1.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_1.CK[0] <= #(tCK) 1'b0;  

        iDDR4_2.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_2.CK[1] <= #(tCK) 1'b1;
        iDDR4_2.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_2.CK[0] <= #(tCK) 1'b0;

        iDDR4_3.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_3.CK[1] <= #(tCK) 1'b1;
        iDDR4_3.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_3.CK[0] <= #(tCK) 1'b0;

        iDDR4_4.CK[1] <= #(tCK/2) 1'b0;
        iDDR4_4.CK[1] <= #(tCK) 1'b1;
        iDDR4_4.CK[0] <= #(tCK/2) 1'b1;
        iDDR4_4.CK[0] <= #(tCK) 1'b0;


        iDDR4_1.ACT_n     <= sig_if.ACT_n;
        iDDR4_1.RAS_n_A16 <= sig_if.RAS_n_A16;
        iDDR4_1.CAS_n_A15 <= sig_if.CAS_n_A15;
        iDDR4_1.WE_n_A14  <= sig_if.WE_n_A14;
        iDDR4_1.ALERT_n   <= sig_if.ALERT_n;
        iDDR4_1.PARITY    <= sig_if.PARITY;
        iDDR4_1.RESET_n   <= sig_if.RESET_n;
        iDDR4_1.TEN       <= sig_if.TEN;
        iDDR4_1.CS_n      <= sig_if.CS_n;
        iDDR4_1.CKE       <= sig_if.CKE;
        iDDR4_1.ODT       <= sig_if.ODT;
        iDDR4_1.C         <= sig_if.C;
        iDDR4_1.BG        <= sig_if.BG;
        iDDR4_1.BA        <= sig_if.BA;
        iDDR4_1.ADDR      <= sig_if.ADDR;
        iDDR4_1.ADDR_17   <= sig_if.ADDR_17;
        iDDR4_1.ZQ        <= sig_if.ZQ;
        iDDR4_1.PWR       <= sig_if.PWR;
        iDDR4_1.VREF_CA   <= sig_if.VREF_CA;
        iDDR4_1.VREF_DQ   <= sig_if.VREF_DQ;

        //DRAM 2
        iDDR4_2.ACT_n     <= sig_if.ACT_n;
        iDDR4_2.RAS_n_A16 <= sig_if.RAS_n_A16;
        iDDR4_2.CAS_n_A15 <= sig_if.CAS_n_A15;
        iDDR4_2.WE_n_A14  <= sig_if.WE_n_A14;
        iDDR4_2.ALERT_n   <= sig_if.ALERT_n;
        iDDR4_2.PARITY    <= sig_if.PARITY;
        iDDR4_2.RESET_n   <= sig_if.RESET_n;
        iDDR4_2.TEN       <= sig_if.TEN;
        iDDR4_2.CS_n      <= sig_if.CS_n;
        iDDR4_2.CKE       <= sig_if.CKE;
        iDDR4_2.ODT       <= sig_if.ODT;
        iDDR4_2.C         <= sig_if.C;
        iDDR4_2.BG        <= sig_if.BG;
        iDDR4_2.BA        <= sig_if.BA;
        iDDR4_2.ADDR      <= sig_if.ADDR;
        iDDR4_2.ADDR_17   <= sig_if.ADDR_17;
        iDDR4_2.ZQ        <= sig_if.ZQ;
        iDDR4_2.PWR       <= sig_if.PWR;
        iDDR4_2.VREF_CA   <= sig_if.VREF_CA;
        iDDR4_2.VREF_DQ   <= sig_if.VREF_DQ;

        //DRAM 3
        iDDR4_3.ACT_n     <= sig_if.ACT_n;
        iDDR4_3.RAS_n_A16 <= sig_if.RAS_n_A16;
        iDDR4_3.CAS_n_A15 <= sig_if.CAS_n_A15;
        iDDR4_3.WE_n_A14  <= sig_if.WE_n_A14;
        iDDR4_3.ALERT_n   <= sig_if.ALERT_n;
        iDDR4_3.PARITY    <= sig_if.PARITY;
        iDDR4_3.RESET_n   <= sig_if.RESET_n;
        iDDR4_3.TEN       <= sig_if.TEN;
        iDDR4_3.CS_n      <= sig_if.CS_n;
        iDDR4_3.CKE       <= sig_if.CKE;
        iDDR4_3.ODT       <= sig_if.ODT;
        iDDR4_3.C         <= sig_if.C;
        iDDR4_3.BG        <= sig_if.BG;
        iDDR4_3.BA        <= sig_if.BA;
        iDDR4_3.ADDR      <= sig_if.ADDR;
        iDDR4_3.ADDR_17   <= sig_if.ADDR_17;
        iDDR4_3.ZQ        <= sig_if.ZQ;
        iDDR4_3.PWR       <= sig_if.PWR;
        iDDR4_3.VREF_CA   <= sig_if.VREF_CA;
        iDDR4_3.VREF_DQ   <= sig_if.VREF_DQ;

        //DRAM 4
        iDDR4_4.ACT_n     <= sig_if.ACT_n;
        iDDR4_4.RAS_n_A16 <= sig_if.RAS_n_A16;
        iDDR4_4.CAS_n_A15 <= sig_if.CAS_n_A15;
        iDDR4_4.WE_n_A14  <= sig_if.WE_n_A14;
        iDDR4_4.ALERT_n   <= sig_if.ALERT_n;
        iDDR4_4.PARITY    <= sig_if.PARITY;
        iDDR4_4.RESET_n   <= sig_if.RESET_n;
        iDDR4_4.TEN       <= sig_if.TEN;
        iDDR4_4.CS_n      <= sig_if.CS_n;
        iDDR4_4.CKE       <= sig_if.CKE;
        iDDR4_4.ODT       <= sig_if.ODT;
        iDDR4_4.C         <= sig_if.C;
        iDDR4_4.BG        <= sig_if.BG;
        iDDR4_4.BA        <= sig_if.BA;
        iDDR4_4.ADDR      <= sig_if.ADDR;
        iDDR4_4.ADDR_17   <= sig_if.ADDR_17;
        iDDR4_4.ZQ        <= sig_if.ZQ;
        iDDR4_4.PWR       <= sig_if.PWR;
        iDDR4_4.VREF_CA   <= sig_if.VREF_CA;
        iDDR4_4.VREF_DQ   <= sig_if.VREF_DQ;
    end

    

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

    //Interface between iDDR4 and data transfer example
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

    assign {
        iDDR4_1.DM_n,
        iDDR4_2.DM_n,
        iDDR4_3.DM_n,
        iDDR4_4.DM_n
    } = dq_en ? {
        dt_if.DM_n,
        dt_if.DM_n,
        dt_if.DM_n,
        dt_if.DM_n
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
    assign dt_if.COL_choice = dc_if.offset; //CHANGE


    // task writing_1();
    //     task_name = "Write 1";
    //     DM_debug = 1'b1;
    //     add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b1), .data(32'hAAAA_AAAA));
    //     data_store1 = 32'h1111_1111;
    //     data_store2 = 32'h2222_2222;
    //     data_store3 = 32'h3333_3333;
    //     data_store4 = 32'h4444_4444;
        
    //     while (!dt_if.wr_en) begin
    //         @(posedge CLK);
    //     end
    //     dt_if.memstore = data_store1;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store1;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store2;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store3;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store4;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'h5555_5555;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'h6666_6666;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'h7777_7777;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'h8888_8888;
    //     @(posedge CLK);
    //     dt_if.clear = 1'b1;
    //     @(posedge CLK);
    //     dt_if.clear = 1'b0;
    // endtask

    // task writing_2();
    //     task_name = "Write 2";
    //     DM_debug = 1'b0;
    //     add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b1), .data(32'hAAAA_AAAA));
    //     data_store1 = 32'hAAAA_AAAA;
    //     data_store2 = 32'hBBBB_BBBB;
    //     data_store3 = 32'hCCCC_CCCC;
    //     data_store4 = 32'hDDDD_DDDD;
    //     while (!dt_if.wr_en) begin
    //         @(posedge CLK);
    //     end
    //     dt_if.memstore = data_store1;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store1;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store2;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store3;
    //     @(posedge CLKx2);
    //     dt_if.memstore = data_store4;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'hAABB_5555;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'hAABB_6666;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'hAABB_7777;
    //     @(posedge CLKx2);
    //     dt_if.memstore = 32'hAABB_8888;
    //     @(posedge CLK);
        
    //     dt_if.clear = 1'b1;
        
    //     @(posedge CLK);
    //     dt_if.clear = 1'b0;
    // endtask

    // task read_chk();
    //     DM_debug = 1'bzz;
    //     task_name = "Add Read";
    //     add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b0), .data(32'hDDCC_BBAA));
    //     //   add_request(.addr({'0, 3'd1,2'b00}), .write(1'b0), .data(32'hDDCC_BBAA));
    //     dq_en = 1'b0;
    //     //   task_name = "Done add Read";
    //     //   repeat (200) @(posedge CLK);
    //     //   task_name = "After 400 cycle Read";
    //     repeat (100) @(posedge CLK);
    // endtask

    initial begin
      iDDR4_1.CK <= 2'b01;
      clk_enb <= 1'b1;
      clk_val <= 1'b1;  
      model_enable_val = 1;
      dq_en = 1'b1;

      nRST = 1'b0;
      @(posedge CLK);
      @(posedge CLK);
      nRST = 1'b1;

      task_name = "Power_up";
      #((tRESET + tPWUP + tRESETCKE + tPDc + tXPR + tDLLKc + tMOD * 7 + tZQinitc) * PERIOD);
      repeat (25) @(posedge CLK);

    //   //Case 1 check the refresh case no interrept
    //   task_name = "Refresh";
    //   repeat (100) @(posedge CLK);
    
    task_name = "Writing_Cycle";
    //Case 2 check the writing cycle
    add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b1), .data(32'hAAAA_AAAA));
    repeat (50) @(posedge CLK);

    
    task_name = "Reading_Cycle";
    dq_en = 1'b0;
    //Case 3 check the reading cycle
    add_request(.addr({16'hAAAA, 8'hAA, 8'b000_000_00}), .write(1'b0), .data(32'hAAAA_AAAA));
    repeat (50) @(posedge CLK);
    


    //   writing_1();
    //   read_chk();
    //   dq_en = 1'b1;
    //   writing_2();
    //   read_chk();
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