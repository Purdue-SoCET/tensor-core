`include "data_transfer_if.vh"
`include "dram_command_if.vh"

module data_transfer (
    input logic CLK,
    input logic nRST,
    data_transfer_if.data_trans mydata
);
    import dram_pack::*;

    // typedef enum logic [1:0] {
    //     IDLE,
    //     SEND_POSE_EDGE,
    //     SEND_NEG_EDGE
    // };
    logic [2:0] count_burst, ncount_burst;
    
    logic [31:0] DQ_latch, nDQ_latch;
    logic [CONFIGURED_DQS_BITS - 1 : 0] DQS_t_latch, nDQS_t_latch;
    logic [CONFIGURED_DQS_BITS - 1 : 0] DQS_c_latch, nDQS_c_latch;

    assign mydata.DQ = (mydata.wr_en) ?   DQ_latch[CONFIGURED_DQ_BITS - 1 : 0] : 'z;
    assign mydata.DQS_t = (mydata.wr_en) ? DQS_t_latch : 'z;
    assign mydata.DQS_c = (mydata.wr_en) ? DQS_c_latch : 'z;
    assign mydata.memload = (count_burst == BURST_LENGTH) ? DQ_latch : '0;

    always_ff @(posedge CLK, negedge CLK, negedge nRST) begin
        if (!nRST) begin
            count_burst <=0;
            DQ_latch <= '0;
            DQS_t_latch <= 1'b0;
            DQS_c_latch <= 1'b0;
        end else begin
            count_burst <= ncount_burst;
            if (mydata.wr_en && (count_burst == 1)) begin
                DQ_latch <= mydata.memstore;
                DQS_t_latch <= 1'b1;
                DQS_c_latch <= 1'b0;
            end 
            else begin
                DQ_latch <= nDQ_latch;
                DQS_t_latch <= nDQS_t_latch;
                DQS_c_latch <= nDQS_c_latch;
            end
            

            
        end
    end

    

    always_comb begin
        ncount_burst = count_burst;
        nDQS_c_latch = DQS_c_latch;
        nDQS_t_latch = DQS_t_latch;
        nDQ_latch = DQ_latch;

        
        if (mydata.wr_en) begin
            ncount_burst = count_burst + 1;
            // nDQ_latch = mydata.memstore;
            if (count_burst > 1) begin
                nDQ_latch = {8'b0, DQ_latch[31:8]};
                nDQS_t_latch = ~DQS_t_latch;
                nDQS_c_latch = ~DQS_c_latch;
            end

        end else if (mydata.rd_en) begin
            ncount_burst = count_burst + 1;
            if (!count_burst) begin
                nDQ_latch = {24'b0, mydata.DQ};
            end
            else if (mydata.DQS_t || mydata.DQS_c) begin
                nDQ_latch = {DQ_latch[23:0], mydata.DQ};
            end
            
        end


        if (mydata.clear) begin
            nDQ_latch = '0;
            nDQS_c_latch = '0;
            nDQS_t_latch = '0;
        end


    end


endmodule