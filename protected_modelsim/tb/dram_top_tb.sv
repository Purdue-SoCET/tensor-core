`include "dram_pkg.vh"
`include "scheduler_buffer_if.vh"
`include "data_transfer_if.vh"
`include "control_unit_if.vh"
`include "signal_gen_if.vh"
`include "arch_defines.v"
`include "dimm.vh"
`timescale 1 ns / 1 ps


//Welcome to the mess, here is just a bunch of code that trying to verify DDR4!
// 1. Test the power up state
// 2. Test the refresh cycle 
// 3. Test row miss write row hit read
// 4. Test row hit write row hit read
// 5. Test the refresh and row miss read
// 6. Test 3 consectutive  row miss write
// 7. Test row conflict write (after 3 consecutive write, I write the conflict row into last row of consecutive writes) (REFRESH happened during writing)
// 8. Test row conflcit read (the last consecutive addr conflict number 7)
// 9. Test 16 consecutive write with different bank
// 10. Test 1000 random read and write of different commands

//RUNING SIMULATION: make dram_top

module dram_top_tb;
    parameter PERIOD = 1.5;
    parameter tCK = 1.5;
    import dram_pkg::*;
    import proj_package::*;

    //parameter from dram_command_if.vh
    parameter CONFIGURED_DQ_BITS     = 8;
    parameter CONFIGURED_DQS_BITS     = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_DM_BITS     = (16 == CONFIGURED_DQ_BITS) ? 2 : 1;
    parameter CONFIGURED_RANKS = 1;
    
    //CLK and debug signals
    logic CLK = 1, nRST;
    logic CLKx2=0;
    reg model_enable_val;
    string task_name;

    //Instantiate the the iDDR4_1 version
    reg clk_val, clk_enb;
    logic DM_debug; //Used it if you want to debug with writing mask
    assign model_enable = model_enable_val;

    //Signal flag to choose write or read
    reg dq_en;
    reg dqs_en;
    

    //Cache signals and signals for verifying the data transmission
    logic cache_write;
    logic cache_read;
    logic [ROW_BITS-1:0] cache_addr;
    logic [2:0] cache_offset;
    logic [63:0] cache_store;
    logic [63:0] cache_load;
    logic don_t_write; //Signals it use for telling whether you want to latch prev addr or not
    logic [31:0] prev_addr; 
    
    //Clock generation of CK and CKx2
    //Issue right now, CK is follow TS_1500 tCK is 1.5ns
    //I want to figure out a way that can change different configurations to choose TS_1500 (right now micron dram is TS_1250 - 1.25ns)
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

    //Instantiate the interface of DRAM controller and DDR4 DRAM
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

    //Instantiate cache as a referrence model to verify data load
    sw_cache CACHE (.CLKx2(CLKx2), .nRST(nRST), .wr_en(cache_write), .rd_en(cache_read), .row_addr(cache_addr), .offset(cache_offset), .dmemstore(cache_store), .dmemload(cache_load));

    //Scheduler interface with the 
    always_comb begin
      dc_if.dREN = (!dc_if.ram_wait) ? 0 : sch_if.ramREN_curr;
      dc_if.dWEN = (!dc_if.ram_wait) ? 0 : sch_if.ramWEN_curr;
      dc_if.ram_addr = sch_if.ramaddr_rq;
      sch_if.request_done = !dc_if.ram_wait;
      //Interface between scheduler buffer and the data_transfer
      dt_if.wr_en = dc_if.wr_en;
      dt_if.rd_en = dc_if.rd_en;
    end

    
    //DRAM interface latch
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
    //Only use 4 chips only, so 32-bit data
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u0_r0(.model_enable(model_enable), .iDDR4(iDDR4_1));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u1_r0(.model_enable(model_enable), .iDDR4(iDDR4_2));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u2_r0(.model_enable(model_enable), .iDDR4(iDDR4_3));
    ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u3_r0(.model_enable(model_enable), .iDDR4(iDDR4_4));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u4_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u4_r0));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u5_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u5_r0));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u6_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u6_r0));
    // ddr4_model #(.CONFIGURED_DQ_BITS(CONFIGURED_DQ_BITS),  .CONFIGURED_RANKS(CONFIGURED_RANKS)) u7_r0(.model_enable(model_enable), .iDDR4(iDDR4_1.u7_r0));

    //Interface between iDDR4 and data transfer example
    // Connect DQ, DQS_t, DQS_c, DM_n
    // Note DM_n is the signal for the writing mask
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

    //Writing mask feature
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

    //Assign these DQ signals back with data transfer (bidirectional)
    assign dt_if.DQS_t = ~dq_en ? iDDR4_1.DQS_t : 1'bz;
    assign dt_if.DQS_c = ~dq_en ? iDDR4_1.DQS_c: 1'bz;
    assign dt_if.DM_n = ~dq_en ? iDDR4_1.DM_n: 1'bz;
    assign dt_if.COL_choice = dc_if.offset; 

    //Latch for the prev_addr, I use this for row hit, row conflict case
    always_ff @(posedge CLK) begin
        if (!nRST) begin
            prev_addr <= 0;
        end else begin
            if (!don_t_write) begin
                prev_addr <= sch.creating_addr;
            end
        end
    end

    //Creating class for the transaction
    class sche_trans;
        //Getting the scheduler buffer interface
        virtual scheduler_buffer_if vif;

        //Random rank, bank group, bank, row, col, offset
        rand logic [RANK_BITS - 1:0] rank;
        // randc logic [BANK_GROUP_BITS - 1:0] BG;
        // randc logic [BANK_BITS - 1:0] bank;
        rand logic [BANK_GROUP_BITS - 1:0] BG;
        rand logic [BANK_BITS - 1:0] bank;
        rand logic [ROW_BITS - 1:0] row;
        rand logic [COLUMN_BITS - 1:0] col;
        rand logic [OFFSET_BITS - 1:0] offset;

        logic [31:0] creating_addr; //the actual address


        //1. Creating covergroup
        covergroup sch_group @(posedge CLK);
            //2.Creating coverpoint
            sch_point : coverpoint {vif.dREN, vif.dWEN} {
                bins s00 = {2'b00};
                bins s10 = {2'b10};
                bins s01 = {2'b01};
            }
        endgroup        

        //3. Creating the constraint
        //dREN and dWEN should never goes high at the same time
        constraint req_cons {
            {vif.dREN, vif.dWEN} != 2'b11;
        }

        //constraint of addr_rank
        constraint addr_rank {
            rank == 1'b0;
            row != '1;
            offset == 0;
            col[2:0] == 0; //8-byte align
        }

        function new (virtual scheduler_buffer_if vif);
            this.vif = vif;
            sch_group = new();
        endfunction

        //function for generate the address
        function gen_addr (string testcase, input logic[31:0] prev_addr);
            //If you want to add row conflict
            if (testcase == "row conflict") begin
                creating_addr = prev_addr;
                creating_addr[30:17] = '1;
            end else if (testcase == "row hit") begin
                creating_addr = prev_addr;
            end else begin
                creating_addr = {rank, row, bank, BG[1], col[9:3], BG[0], col[2:0], offset};
            end
        endfunction
    endclass

    //Class for generate data (This is not necessary)
    class creating_dt;
        rand logic [31:0] data_store;
        function new ();

        endfunction
        function display;
            $display ("data_store %0x", data_store);
        endfunction
    endclass

    //Define class
    creating_dt dt_class;   
    sche_trans sch;

    //Use this task to add a request into scheduler FIFO
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
      sch_if.dWEN = 1'b0;
      sch_if.dREN = 1'b0;
    endtask

    //This is the task you want to write something in a specific addr
    //Don't worry about the data context
    task writing_1(input logic [31:0] addr, input creating_dt dt_class);
        begin
        add_request(.addr(addr), .write(1'b1), .data(32'hAAAA_AAAA));
        while (!dt_if.wr_en) begin
            @(posedge CLK);
        end

        //This loop will wriete
        for (int i = 0; i < 9; i++) begin
            dt_class.randomize();
            // dt_class.display();
            dt_if.memstore = dt_class.data_store;
            // $display ("Here is  i : %0x, and memstore: %0x", i, dt_class.data_store);
            if (i != 0) begin
                cache_addr = addr[30:16];
                cache_write = 1'b1;
                cache_store = dt_class.data_store;
                cache_offset = i - 1;
            end
            @(posedge CLKx2);
        end
        dt_if.clear = 1'b1; //Should not be here, check later this
        cache_write = 1'b0;
        @(posedge CLK);
        dt_if.clear = 1'b0;
        end
    endtask

    //A random testing case
    task writing_read_row_hit(input creating_dt dt_class);
        task_name = "Writing_Cycle";
        //Case 2 check the writing cycle
        //Case checking the writing burst
        //Creating new addr
        sch.randomize();
        sch.gen_addr("row miss", prev_addr);
        writing_1(sch.creating_addr, dt_class);
        repeat (50) @(posedge CLK);

        task_name = "Reading_Cycle";
        dq_en = 1'b0;
        //Case 3 check the reading cycle
        add_request(.addr(sch.creating_addr), .write(1'b0), .data(32'hAAAA_AAAA));
        repeat (50) @(posedge CLK);
    endtask

    //This is the task where you want to read the address and verify with cache model
    task read_with_verify (
        input logic [31:0] addr,
        input sche_trans sch
    );
        dq_en = 0;
        add_request(.addr(addr), .write(1'b0), .data(32'hAAAA_AAAA));
        while (dc_if.ram_wait) begin
            cache_read = 1;
            cache_addr = addr[30:16];
            if (dt_if.edge_flag) begin
                cache_offset = cache_offset + 1;
                @(posedge CLKx2);
            end else begin
                cache_offset = 0;
                @(posedge CLKx2);
            end
        end
        dq_en = 1;
        cache_read = 1;
        dt_if.clear = 0;
    endtask
    //Creating the assert to check the failed case of data load
    property wr_verify;
        @(posedge CLK) disable iff (!nRST)
        dt_if.rd_en && (dt_if.edge_flag) |-> (cache_load == dt_if.memload);
    endproperty
    assert property (wr_verify)
    else 
        //If failed it should stop simulation
        $fatal("Time: [%0t], Addr: %0x, offset: %0x, cache load: %0x, dt_memload: %0x",$time,sch.creating_addr[30:16], cache_offset, cache_load, dt_if.memload);


    //Task of writing different 16 writes of different banks
    task consecutive_16_write();
        for (int i = 0; i < 16; i++) begin
            task_name = $sformatf("16 write-dif bank  -%0d", i);
            dq_en = 1'b1;
            sch.randomize();
            sch.gen_addr("row miss", prev_addr);
            writing_1(sch.creating_addr, dt_class);
            while (dc_if.ram_wait) begin
                @(posedge CLK);
            end
        end
    endtask

    //1000 request come one by one
    task random_req();
        bit wr_or_rd; 
        for (int i = 0; i < 1000; i++) begin
            task_name = $sformatf("Task random -%0d", i);
            wr_or_rd = $urandom_range(0,1); // simple 0/1;
            if (wr_or_rd) begin
                dq_en = 1'b1;
                sch.randomize();
                sch.gen_addr("row miss", prev_addr);
                writing_1(sch.creating_addr, dt_class);
                while (dc_if.ram_wait) begin
                    @(posedge CLK);
                end
            end else begin
                dq_en = 1'b0;
                read_with_verify(sch.creating_addr, sch);
            end 
        end
    endtask

    initial begin
      iDDR4_1.CK = 2'b01;
      clk_enb = 1'b1;
      clk_val = 1'b1;  
      model_enable_val = 1;
      dq_en = 1'b1;
      don_t_write = 0;
      
      //Cache
      cache_addr = 0;
      cache_write = 0;
      cache_read = 0;
      cache_offset = 0;
      cache_store = 0;
      
      
      dt_class = new();
      sch = new(sch_if);
      nRST = 1'b0;
      @(posedge CLK);
      @(posedge CLK);
      nRST = 1'b1;

      
      task_name = "Power_up";
      #((tRESET + tPWUP + tRESETCKE + tPDc + tXPR + tDLLKc + tMOD * 7 + tZQinitc) * PERIOD);
      repeat (25) @(posedge CLK);

    
    
    task_name = "Writing_Cycle";
    sch.randomize();
    sch.gen_addr("row miss", prev_addr);
    writing_1(sch.creating_addr, dt_class);
    repeat (50) @(posedge CLK);

    
    task_name = "Reading_Cycle";
    dq_en = 1'b0;
    read_with_verify(sch.creating_addr, sch);
    
    
    //checking the write - write - read row hit
    task_name = "write - write - read - row hit";
    dq_en = 1'b1;
    writing_1(prev_addr, dt_class);
    while (dc_if.ram_wait) begin
        @(posedge CLK);
    end
    repeat(10) @(posedge CLK);
    read_with_verify(prev_addr, sch);
    

    //Case wait for refreshing refresh everything
    task_name = "refresh 150 cycles";
    repeat(150) @(posedge CLK);
    //PASS CHECKPOINT

    // For the purpose of checking the refresh command
    // We will load the same address and observe
    // 1. Command FSM IDLE -> ACT -> READ
    // 2. Row policy is updated
    read_with_verify(prev_addr, sch);

    //Test case: Testing row miss case with 3 consecutive writes of random address
    task_name = "3 consectutive writing";
    dq_en = 1'b1;
    //1 consectutive
    sch.randomize();
    sch.gen_addr("row miss", prev_addr);
    writing_1(sch.creating_addr, dt_class);
    while (dc_if.ram_wait) begin
        @(posedge CLK);
    end
    repeat(10) @(posedge CLK);

    //2 consectutive
    sch.randomize();
    sch.gen_addr("row miss", prev_addr);
    writing_1(sch.creating_addr, dt_class);
    while (dc_if.ram_wait) begin
        @(posedge CLK);
    end
    repeat(10) @(posedge CLK);

    //3 consectutive
    task_name = "The last consecutive write of the testcase";
    sch.randomize();
    sch.gen_addr("row miss", prev_addr);
    writing_1(sch.creating_addr, dt_class);
    while (dc_if.ram_wait) begin
        @(posedge CLK);
    end
    repeat(10) @(posedge CLK);


    //After that we use the last consecutive write to test the conflict case
    task_name = "Test row conflict write row hit read";
    don_t_write = 1'b1;
    sch.gen_addr("row conflict", prev_addr);
    writing_1(sch.creating_addr, dt_class);
    while(dc_if.ram_wait) begin
        @(posedge CLK);
    end
    repeat(10) @(posedge CLK);

    //This task is special because after 3 consecutive writes, and while reading, we jump into refresh request
    task_name = "Test row conflcit read (the old address that cause write)";
    read_with_verify(prev_addr, sch);
    repeat(200) @(posedge CLK);

    //Task 16_consecutive writes
    task_name = "16 write-dif bank";
    consecutive_16_write();

    //Task random
    random_req();

    //CHECKPOINT: DONE ALL PREVIOUS CASES
    //TODO may be: the writing burst mask cases doesn't have general test cases
    $finish;
    end
endmodule


//Reference cache for verification
//Use to store 64byte of data in different rows
module sw_cache #( parameter ROW_BITS = 15)
(
    input logic CLKx2,
    input logic nRST,
    input logic wr_en,
    input logic rd_en,
    input logic [ROW_BITS-1:0] row_addr,
    input logic [2:0] offset,
    input logic [63:0] dmemstore,
    output logic [63:0] dmemload
);

    typedef struct packed {
        logic [7:0][63:0] arr;
    } data_8bytes;

    data_8bytes sw_cache [2**ROW_BITS-1:0];

    always_ff @(posedge CLKx2, negedge nRST) begin
        if(!nRST) begin
            for (int i = 0; i < ROW_BITS; i++) begin
                sw_cache[i] <= 0;
            end
        end else begin
            if (wr_en) begin
                sw_cache[row_addr].arr[offset] <= dmemstore;
            end
        end
    end

    always_comb begin
        dmemload = 0;
        if (rd_en) begin
            dmemload = sw_cache[row_addr].arr[offset];
        end
    end
endmodule