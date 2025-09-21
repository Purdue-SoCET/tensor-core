`timescale 1ns/1ps
`include "command_FSM_if.vh"

module command_FSM (
    input logic CLK,
    input logic nRST,
    command_FSM_if.dut mycmd
);
    import dram_pack::*;
    localparam logic [1:0] IDLE_R = 2'b00;
    localparam logic [1:0] HIT = 2'b01;
    localparam logic [1:0] MISS = 2'b10;
    localparam logic [1:0] CONFLICT = 2'b11;
    

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            mycmd.cmd_state <= POWER_UP;
        end else begin
            mycmd.cmd_state <= mycmd.ncmd_state;
        end
    end

    always_comb begin
        mycmd.ncmd_state = mycmd.cmd_state;
        mycmd.row_resolve = 1'b0;
        mycmd.init_req = 0;
        casez (mycmd.cmd_state)

            POWER_UP: begin
                mycmd.init_req = 1;
                if (mycmd.init_done) mycmd.ncmd_state = IDLE;
            end

            REFRESH: begin
                //todo after tREF done should it go back to original state or IDLE
                if (mycmd.tREF_done) begin
                    mycmd.ncmd_state = IDLE;     
                end
            end

            IDLE: begin
                if (mycmd.rf_req) mycmd.ncmd_state = REFRESH;
                else if (mycmd.dWEN || mycmd.dREN) begin
                    if (mycmd.row_stat == HIT) mycmd.ncmd_state = mycmd.dWEN ? WRITE : READ;
                    else if(mycmd.row_stat == CONFLICT) mycmd.ncmd_state = PRECHARGE;
                    else if (mycmd.row_stat == MISS) mycmd.ncmd_state = ACTIVATE;
                end
            end

            ACTIVATE: begin
                if (mycmd.rf_req) begin mycmd.ncmd_state = REFRESH;end
                else begin mycmd.ncmd_state = ACTIVATING; end
            end

            ACTIVATING: begin
                if (mycmd.tACT_done) begin
                    mycmd.ncmd_state = mycmd.rf_req ? PRECHARGE : mycmd.dWEN ? WRITE : READ;
                end
            end

            WRITE: begin mycmd.ncmd_state = mycmd.rf_req ? PRECHARGE : WRITING; end
            READ : begin mycmd.ncmd_state = mycmd.rf_req ? PRECHARGE : READING; end
            
            WRITING: begin
                if (mycmd.tWR_done) begin
                    if (mycmd.rf_req) begin mycmd.ncmd_state = PRECHARGE; end
                    else if (mycmd.dWEN || mycmd.dREN) begin
                        if (mycmd.row_stat == HIT) mycmd.ncmd_state = mycmd.dWEN ? WRITE : READ;
                        else if(mycmd.row_stat == CONFLICT) mycmd.ncmd_state = PRECHARGE;
                        else if (mycmd.row_stat == MISS) mycmd.ncmd_state = ACTIVATE;
                    end 
                    else begin
                        mycmd.ncmd_state = IDLE;
                    end 
                end
            end

            READING: begin
                if (mycmd.tRD_done) begin
                    if (mycmd.rf_req) begin mycmd.ncmd_state = PRECHARGE; end
                    else if (mycmd.dWEN || mycmd.dREN) begin
                        if (mycmd.row_stat == HIT) mycmd.ncmd_state = mycmd.dWEN ? WRITE : READ;
                        else if(mycmd.row_stat == CONFLICT) mycmd.ncmd_state = PRECHARGE;
                        else if (mycmd.row_stat == MISS) mycmd.ncmd_state = ACTIVATE;
                    end
                end else begin
                    mycmd.ncmd_state = IDLE;
                end 
            end

            PRECHARGE: begin
                mycmd.row_resolve = 1'b1;
                if (mycmd.tPRE_done) begin
                    mycmd.ncmd_state = mycmd.rf_req ? REFRESH : IDLE;
                end
            end
        endcase
    end

endmodule
