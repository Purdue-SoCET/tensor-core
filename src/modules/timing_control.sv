`include "dram_pkg.vh"
`include "timing_signals_if.vh"
`include "command_fsm_if.vh"

module timing_control (
    input logic clk, nRST,
    timing_signals_if.timing_ctrl timif
    command_fsm_if.timing_control cfsmif
);
    // time counter signals
    parameter N = 5;
    logic [N-1:0] time_load, time_count;
    logic time_count_done;

    always_comb begin
        timif.tACT_done = 1'b0;
        timif.tWR_done = 1'b0;
        timif.tRD_done = 1'b0;
        timif.tPRE_done = 1'b0;
        timif.tREF_done = 1'b0;
        timif.rf_req = 1'b0;
        
        time_counter_en = 1'b0;
        time_LOAD = '0;
        wr_en = 1'b0;

        case (cfsmif.cmd_state)
            ACTIVATE : begin
                time_counter_en = 1'b1;
                
                if (timif.rf_req == 1'b1) begin         // ACT -> PRE time for refresh requests
                    time_load = tRAS;
                end

                else begin                              // ACT -> READ/WRITE time
                    time_load = tRCD - tAL;             // tAL = 0 if AL command not set. Only tRCD is a safer option
                end

                // TODO for consecutive commands
                // tRRD for consecutive activates
                // tFAW for 4 consecutive activates with tRRD_s? (Need to check if only tRRD_s or tRRD_l as well)
                // tRC for ACT -> ACT / REF commands to same bank
                
            end

            ACTIVATING : begin
                if (time_count_done == 1'b1) begin
                    timif.tACT_done = 1'b1;
                    time_counter_en = 1'b0;
                end
            end

            READ : begin
                time_counter_en = 1'b1;
                time_load = tRL + tBURST;

                // TODO for consecutive reads
                // tCCD_S = diff BG
                // tCCD_L = same BG
            end

            READING : begin
                if (time_count_done == 1'b1) begin
                    timif.tRD_done = 1'b1;
                    time_counter_en = 1'b0;
                end
            end

            WRITE : begin
                time_counter_en = 1'b1;
                time_load = tWL + tBURST;

                // TODO for consecutive writes
                // tCCD_S = diff BG
                // tCCD_L = same BG
            end

            WRITING : begin
                if (time_count == tWL) begin
                    wr_en = 1'b1;
                end
	                
                if (time_count_done == 1'b1) begin
	                timif.tWR_done = 1'b1;
                    time_counter_en = 1'b0; 
                end
            end

            PRE : begin
                time_counter_en = 1'b1;
                time_load = tRP;

                if (time_count_done == 1'b1) begin
                    timif.tPRE_done = 1'b1;
                    time_counter_en = 1'b0;
                end
            end

        endcase
    end

    flex_counter #(.N(N)) time_counter (.clk(clk), .nRST(nRST), .enable(yime_counter_en),
                                        .count_load(time_load), .count(time_count), 
                                        .count_done(time_count_done));
endmodule