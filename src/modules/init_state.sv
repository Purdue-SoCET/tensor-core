`timescale 1ns/1ps

`include "init_state_if.vh"
`include "socetlib_counter_if.vh"
module init_state (
    input logic CLK, nRST,
    init_state_if.dt it
);

    import dram_pkg::*;

    logic [11:0] timing_count, timing_value, ntiming_vallue;
    logic timing_clear, timing_cnt_en, timing_flag, n_timing_cnt_en;

    //Latch init_valid;
    logic n_init_valid;
    dram_state_t state, n_state;
    socetlib_counter #(.NBITS(12)) time_counter (
        .CLK(CLK),
        .nRST(nRST),
        .clear(timing_clear),
        .count_enable(timing_cnt_en),
        .overflow_val(timing_value),
        .count_out(timing_count),
        .overflow_flag(timing_flag)
    );

    assign it.init_state = state;
    

    always_ff @(posedge CLK, negedge nRST) begin: dram_state_t_logic
        if (!nRST) begin
            state <= POWER_UP;
            timing_cnt_en <= 0;
            it.init_valid <= 0;
        end else begin
            state <= n_state;
            timing_cnt_en <= n_timing_cnt_en;            
            it.init_valid <= n_init_valid;
        end
    end

    always_comb begin: INIT_DRAM_STATE
        n_state = state;
        timing_clear = 0;
        n_timing_cnt_en = timing_cnt_en;
        timing_value =  0;
        n_init_valid = it.init_valid;
        case(state)
            POWER_UP: begin
                timing_value = tPWUP;
                if (it.init) begin
                    n_timing_cnt_en = 1'b1;
                end
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = PRE_RESET;
                end
            end

            PRE_RESET: begin
                timing_value = tPWUP;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = RESET;
                end

            end

            RESET: begin
                timing_value = tPWUP;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = NOP;
                end

            end

            NOP: begin 
                timing_value = tPDc + tXPR;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_MODE_DLL;
                end

            end

            LOAD_MODE_DLL: begin
                timing_value = tDLLKc;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG0_REG3;
                end

            end
        
            LOAD_BG0_REG3: begin 
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG1_REG6;
                end
            end

            LOAD_BG1_REG6: begin
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG1_REG5;
                end
            end
            LOAD_BG1_REG5: begin 
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG1_REG4;
                end
            end
            LOAD_BG1_REG4: begin 
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG0_REG2;
                end
            end
            LOAD_BG0_REG2: begin 
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG0_REG1;
                end
            end
            LOAD_BG0_REG1: begin 
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = LOAD_BG0_REG0;
                end
            end
            LOAD_BG0_REG0: begin 
                timing_value = tMOD;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_state = ZQ_CL;
                end

            end
            ZQ_CL: begin 
               timing_value = tZQinitc;
                if (timing_flag) begin
                    timing_clear = 1;
                    n_init_valid = 1;
                    n_state = IDLE;
                    n_timing_cnt_en = 1'b0;
                end 
            end

            //Start to working on between IDLE, ACTIVATE, WRITE, PRECHARGE, WRITE_COMMAND, READ_COMMAND
            IDLE: begin
                
            end
        endcase
        
    end
endmodule