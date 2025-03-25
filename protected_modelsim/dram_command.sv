`include "dram_command_if.vh"


module dram_command (
    input logic CLK,
    input logic nRST,
    dram_command_if.dram_command_RAM dr_ram,
    dram_command_if.dram_command_sche_buff dr_sche
);

    dram_state_t state, n_state;
    logic [11:0] rollover_value;

    logic [11:0] timing_count, n_timing_count;
    logic [4:0] cmd_addr;

    logic [2:0] count_act, n_count_act;

    always_ff @(posedge CLK, negedge nRST) begin: ACT_n
        if(!nRST) begin
            count_act <= '0;
        end else begin
            count_act <= n_count_act;
        end

    end

    always_ff @(posedge CLK, negedge nRST) begin : timing_trk_logic
        if (!nRST) begin
            timing_count <= '0;
        end else begin
            timing_count <= n_timing_count;
        end
    end

    //The tb update every negative edge of the clock not so sure why
    always_ff @(posedge CLK, negedge nRST) begin: dram_state_t
        if (!nRST) begin
            state <= POWER_UP;
        end else begin
            state <= n_state;
        end

    end

    always_comb begin : Next_state_logic_DRAM
        n_state = state;
        n_count_act = count_act;
        act_not_5 = 1'b1;
        n_timing_count = timing_count + 12'd1;
        

        if (count_act == 3'd5) begin
            act_not_5 = 1'b0;
        end

        
        case (state)
            POWER_UP: begin
                n_state = timing_count == rollover_value ? PRE_RESET : POWER_UP;
                
            end
            PRE_RESET: begin 
                n_state = timing_count == rollover_value ? RESET : PRE_RESET; 

            end
            RESET: begin 
                n_state = timing_count == rollover_value ? NOP : RESET; 
            end
            NOP: begin 
                n_state = timing_count == rollover_value ? LOAD_BG1_REG1 : NOP; 
            end
            LOAD_BG0_REG1: begin 
                n_state = timing_count == rollover_value ? LOAD_BG0_REG3 : LOAD_BG0_REG1; 
            end
            LOAD_BG0_REG3: begin 
                n_state = timing_count == rollover_value ? LOAD_BG1_REG6 : LOAD_BG0_REG3; 
            end

            LOAD_BG1_REG6: begin
                 n_state = timing_count == rollover_value ? LOAD_BG1_REG5 : LOAD_BG1_REG6;
            end
            LOAD_BG1_REG5: begin 
                n_state = timing_count == rollover_value ? LOAD_BG1_REG4 : LOAD_BG1_REG5; 
            end
            LOAD_BG1_REG4: begin 
                n_state = timing_count == rollover_value ? LOAD_BG0_REG2 : LOAD_BG1_REG4; 
            end
            LOAD_BG0_REG2: begin 
                n_state = timing_count == rollover_value ? LOAD_BG0_REG1 : LOAD_BG0_REG2; 
            end
            LOAD_BG0_REG1: begin 
                n_state = timing_count == rollover_value ? LOAD_BG0_REG0 : LOAD_BG0_REG1;
            end
            LOAD_BG0_REG0: begin 
                n_state = timing_count == rollover_value ? ZQ_CL : LOAD_BG0_REG0;
            end
            ZQ_CL: begin 
                n_state = timing_count == rollover_value ? IDLE : ZQ_CL;
            end


            //Start to working on between IDLE, ACTIVATE, WRITE, PRECHARGE, WRITE_COMMAND, READ_COMMAND
            IDLE: begin
                if (!dr_sche.REFRESH && dr_sche.dWEN_curr || dr_sche.dREN_curr) begin
                    n_state = ACTIVATE;
                end else if (dr_sche.REFRESH) begin
                    n_state = IDLE; //This shoudl be refresh case
                end
            end
            ACTIVATE: begin
                if (dr_sche.REFRESH) begin
                    n_state = PRECHARGE;
                    n_count_act = 3'd1;
                end
                else if (!act_not_5) begin
                    n_state = PRECHARGE;
                end
                else if (dr_sche.dWEN_curr && timing_count == rollover_value) begin
                    n_state = WRITE_COMMAND;
                    n_count_act = 3'd1;
                end else if (dr_sche.dREN_curr && timing_count == rollover_value) begin
                    n_state = READ_COMMAND;
                    n_count_act = 3'd1;
                end else if (dr_sche.B0 != dr_sche.B1) begin
                    n_count_act = count_act + 3'd1;
                    n_state = state;
                end
            end
            WRITE_COMMAND: begin
                if (dr_sche.REFRESH && timing_count == rollover_value) begin
                    n_state = PRECHARGE;
                end else if (dr_sche.dREN_curr && timing_count == rollover_value) begin
                    n_state = READ_COMMAND;
                end else if ((dr_sche.Ra0 != dr_sche.Ra1 && dr_sche.R0 == dr_sche.R1) || (dr_sche.B0 == dr_sche.B1 && dr_sche.Ra0 == dr_sche.Ra1) && (timing_count == rollover_value) && dr_sche.dWEN_ftrt) begin
                    n_state = WRITE_COMMAND;
                end
                else if (timing_count == rollover_value) begin
                    n_state = PRECHARGE;
                end
            end

            READ_COMMAND: begin 
                if (dr_sche.REFRESH && timing_count == rollover_value) begin
                    n_state = PRE_CHARGE;
                end else if (dr_sche.dWEN_curr && timing_count == rollover_value) begin
                    n_state = WRITE_COMMAND;
                end else if (dr_sche.dREN_ftrt && (dr_sche.R0 == dr_sche.R1 && dr_sche.B0 == dr_sche.B1 && dr_sche.Ra0 == dr_sche.Ra1)) begin
                    n_state = state;
                end
                else if (timing_count == rollover_value) begin
                    n_state = PRE_CHARGE;
                end
            end 

            PRECHARGE: begin
                n_count_act = 3'd0;
                if ((dr_sche.dREN_curr || dr_sche.dWEN_curr) && (timing_count == rollover_value) && !dr_sche.REFRESH) begin
                    n_state = ACTIVATE;
                end else if (timing_count == rollover_value) begin
                    n_state = IDLE;
                end
            end
        endcase

        if (state != n_state) begin
            n_timing_count = 12'd1;
        end
    end


    always_comb begin : OUTPUT_VALUE
        //Default value
        cmd_addr = DESEL_CMD;
        dr_ram.ALERT_n = '1;
        dr_ram.PARITY =  '0;
        dr_ram.RESET_n = 1'b1;
        dr_ram.TEN = '0;
        dr_ram.ODT = '0;
        dr_ram.C = '0;
        dr_ram.BG = '0;
        dr_ram.BA = '0;
        dr_ram.ADDR =  '0;
        dr_ram.RAS_n_A16 = '1;
        dr_ram.CAS_n_A15 = '1;
        dr_ram.WE_n_A14 = '1;
        dr_ram.ADDR_17 = '0;

        dr_sche.data_callback = '0;
        dr_sche.request_done = 1'b0;
        

        case (state)
            POWER_UP: begin
                cmd_ddr = POWER_UP_PRG;
                dr_ram.CKE = 0;
                dr_ram.TEN = 0;
                dr_ram.PARITY = 0;
                dr_ram.ALERT_n = 1;
                dr_ram.RESET_n = 0;
                dr_ram.ZQ = 0;
                dr_ram.PWR = 0;
                dr_ram.VREF_CA = 0;
                dr_ram.VREF_DQ = 0;
            end
            PRE_RESET: begin
                cmd_ddr = POWER_UP_PRG;
                dr_ram.CKE = 0;
                dr_ram.TEN = 0;
                dr_ram.PARITY = 0;
                dr_ram.ALERT_n = 1;
                dr_ram.RESET_n = 0;
                dr_ram.ZQ = 0;
                dr_ram.PWR = 1;
                dr_ram.VREF_CA = 1;
                dr_ram.VREF_DQ = 1;
            end
            RESET: begin
                dr_ram.RESET_n = 1;
            end
            NOP: begin
                cmd_addr = DESEL_CMD;
            end
            LOAD_BG0_REG1: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h0;
                    dr_ram.BA       = 2'h1;
                    dr_ram.ADDR     = 14'h1;
                end
            end
            LOAD_BG0_REG3: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h0;
                    dr_ram.BA       = 2'h3;
                    dr_ram.ADDR     = 14'h0;
                end
            end
            LOAD_BG1_REG6: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h1;
                    dr_ram.BA       = 2'h2;
                    dr_ram.ADDR     = 14'h080F;
                end
            end
            LOAD_BG1_REG5: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h1;
                    dr_ram.BA       = 2'h1;
                    dr_ram.ADDR     = 14'h0;
                end
            end
            LOAD_BG1_REG4: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h1;
                    dr_ram.BA       = 2'h0;
                    dr_ram.ADDR     = 14'h1000;
                end
            end
            LOAD_BG0_REG2: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    BG       = 2'h0;
                    BA       = 2'h2;
                    ADDR     = 14'h0088;
                end
            end
            LOAD_BG0_REG1: begin 
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h0;
                    dr_ram.BA       = 2'h1;
                    dr_ram.ADDR     = 14'h0001;
                end
            end
            LOAD_BG0_REG0: begin
                if (timing_count < 2) begin
                    cmd_addr = LOAD_MODE_CMD;
                    dr_ram.BG       = 2'h0;
                    dr_ram.BA       = 2'h0;
                    dr_ram.ADDR     = 14'h0041d;
                end
            end
            ZQ_CL: begin
                if (timing_count < 2) begin
                    cmd_addr = ZQ_CMD;
                    dr_ram.ADDR = 14'h0400;
                end
            end
            IDLE: begin
                cmd_addr = NOP_CMD;
            end
            ACTIVATE: begin
                if (timing_count < 2) begin
                    cmd_addr = ACTIVATE_CMD;
                    dr_ram.BG = dr_sche.BG0;
                    dr_ram.BA = dr_sche.BA0;
                    dr_ram.RAS_n_A16 = dr_sche.R0[16]; 
                    dr_ram.CAS_n_A15 = dr_sche.R0[15];
                    dr_ram.WE_n_A14 =  dr_sche.R0[14];
                    dr_ram.ADDR =      dr_sche.R0[13:0];
                end
            end
            WRITE_COMMAND: begin
                if (timing_count < 2) begin
                    cmd_addr = WRITE_CMD;
                    dr_ram.BG = dr_sche.BG0;
                    dr_ram.BA = dr_sche.BA0;
                    dr_ram.RAS_n_A16 = 1'b1; 
                    dr_ram.CAS_n_A15 = 1'b0;
                    dr_ram.WE_n_A14 =  1'b0;
                    dr_ram.ADDR = {1'b0, FLY_BY, 1'b0, NO_AUTO_PRE, dr_sche.COL0};
                end
            end
            READ_COMMAND: begin
                if (timing_count < 2) begin
                    cmd_addr = READ_CMD;
                    dr_ram.BG = dr_sche.BG0;
                    dr_ram.BA = dr_sche.BA0;
                    dr_ram.RAS_n_A16 = 1'b1; 
                    dr_ram.CAS_n_A15 = 1'b0;
                    dr_ram.WE_n_A14 =  1'b1;
                    dr_ram.ADDR = {1'b0, FLY_BY, 1'b0, NO_AUTO_PRE, dr_sche.COL0};
                end

            end
            PRECHARGE: begin
                if (timing_count < 2) begin
                    cmd_addr = PRE_CMD;
                    dr_ram.BG = dr_sche.BG0;
                    dr_ram.BA = dr_sche.BA0;
                    dr_ram.ADDR[10] = 1'b0;
                end
            end

            default: ;
            
        endcase        
    end

    always_comb begin : CONTROL_TIME
        rollover_value = 32'd3000;
        case (state)
            POWER_UP, PRE_RESET, RESET: begin rollover_value = tPWUP; end
            NOP: begin rollover_value = tPDc; end
            LOAD_BG0_REG0,
            LOAD_BG0_REG1,
            LOAD_BG0_REG2,
            LOAD_BG0_REG3,
            LOAD_BG1_REG1,
            LOAD_BG1_REG4,
            LOAD_BG1_REG5,
            LOAD_BG1_REG6: begin rollover_value = tMOD; end
            ZQ_CL: begin rollover_value = tZQinitc; end


            ACTIVATE: begin
                if (act_not_5) begin
                    if (dr_sche.dREN_curr || dr_sche.dWEN_curr) begin
                        rollover_value = tRCD;
                    end 
                    else if (dr_sche.BG0 != dr_sche.BG1) begin
                        rollover_value = tRRD_S;
                    end else begin
                        rollover_value = tRRD_L;    
                    end
                end else begin
                        rollover_value = tFAW; //This is meant act is 5
                end
            end            //Read and write and activation command
            READ_COMMAND: begin
                if (dr_sche.dREN_ftrt && dr_sche.Ra0 != dr_sche.Ra1) begin
                    rollover_value = tBURST + tRTRS;
                end
                else if (dr_sche.dWEN_ftrt && dr_sche.R0 == dr_sche.R1) begin
                    rollover_value = tCAS + tBURST + tRTRS - tCWD;     
                end
                else if (dr_sche.B0 != dr_sche.B1 && dr_sche.R0 != dr_sche.R1) begin
                    rollover_value = 2;
                end
                else begin
                    rollover_value = tCAS + tBURST;
                end 
            end

            WRITE_COMMAND: begin
                if (dr_sche.BG0 != dr_sche.BG1 && dr_sche.Ra0 == dr_sche.Ra1 && dr_sche.dWEN_ftrt) begin
                    rollover_value = tCCD_S;
                end else if (dr_sche.BG0 != dr_sche.BG1 && dr_sche.Ra0 == dr_sche.Ra1 && dr_sche.dWEN_ftrt) begin
                    rollover_value = tCCD_L;
                end
                else if (dr_sche.Ra0 != dr_sche.Ra1 && dr_sche.R0 == dr_sche.R1 && dr_sche.dWEN_ftrt) begin
                    rollover_value = tCWD + tBURST + tOST + tBURST;
                end else if (dr_sche.Ra0 != dr_sche.Ra1 && dr_sche.R0 != dr_sche.R1 && dr_sche.dWEN_ftrt) begin
                    rollover_value = tCWD;

                end else if (dr_sche.Ra1 == dr_sche.Ra0 && dr_sche.R0 == dr_sche.R1 && dr_sche.dREN_ftrt) begin
                    rollover_value = tCWD + tBURST + tWTR;
                end else if (dr_sche.Ra1 != dr_sche.Ra0 && dr_sche.R0 == dr_sche.R1 && dr_sche.dREN_ftrt) begin
                    rollover_value = tCWD + tBURST + tRTRS;
                end
                else begin 
                    rollover_value = tWL + tWR + tBURST;                     
                end
            end

            PRE_CHARGE: begin
                rollover_value = tRP;
            end

            default:;

        endcase
        
    end

    assign {dr_ram.CK_n, dr_ram.ACT_n, dr_ram.RAS_n_A16, dr_ram.CAS_n_A15, dr_ram.WE_n_A14} = cmd_addr;


endmodule