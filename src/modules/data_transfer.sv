`include "data_transfer_if.vh"
`include "edge_det_if.vh"
`include "dram_command_if.vh"

module data_transfer (
    input logic CLK,
    input logic CLKx2,
    input logic nRST,
    data_transfer_if.data_trans mydata
);
    import dram_pack::*;
    parameter BURST = 8;
    edge_det_if myedge();
    logic [3:0] count_burst, ncount_burst, cnt1;
    logic wr_en1, wr_en2; //We may need this to latch then count the burst
    
    logic select_low;
    logic [CONFIGURED_DQS_BITS - 1 : 0] DQS_t_1, DQS_t_2, nDQS_t;
    logic edge_flag;
    logic [3:0] COL_choice_tr;
    
    
    //WRITING CASE: 
    logic [31:0] DQ_up, D_in, D_out, D_mux;
    logic [7:0][31:0] word_register;
    //READING CASE:


    assign mydata.DQ = (mydata.wr_en) ?    DQ_up : 'z;
    assign mydata.DQS_t = (mydata.wr_en) ? DQS_t_2 : 'z;
    assign mydata.DQS_c = (mydata.wr_en) ? ~DQS_t_2 : 'z;
    assign mydata.DM_n = (mydata.wr_en) ? !(count_burst == COL_choice_tr) : 1'bz;
    assign mydata.memload = (count_burst == (BURST + 4'd2)) ? word_register[mydata.COL_choice] : '0;
    assign COL_choice_tr = mydata.COL_choice + 4'd4; 


    //Interface between DQS_t and the edge_det
    assign myedge.async_in = mydata.DQS_t; 
    assign edge_flag = myedge.edge_flag;   

    edge_det #(.TRIG_RISE(1'b1), .TRIG_FALL(1'b1)) u0 (.clk(CLKx2), .n_rst(nRST), .myedge(myedge));

    always_ff @(posedge CLKx2, negedge nRST) begin
        if (!nRST) begin
            count_burst <= '0;
            cnt1 <= '0;
            DQS_t_2 <= 1;
        end else begin
            if (mydata.wr_en ) begin
                count_burst <= ncount_burst;
                cnt1 <= count_burst;
            end else if (mydata.rd_en) begin
                count_burst <= ncount_burst;
            end
            if (mydata.clear) begin
                count_burst <= '0;
            end
            DQS_t_2 = nDQS_t;
        end
    end

    


    always_ff @(negedge CLKx2, negedge nRST) begin //BURST_EVEN
        if (!nRST) begin
            DQ_up <= '0;
        end else begin
            if (mydata.wr_en && (count_burst >= 4'd3)) begin
                DQ_up <= mydata.memstore;    
            end
            
        end
    end


    always_ff @(posedge CLKx2, negedge nRST) begin
        if (!nRST) begin
            word_register <= '0;
        end else begin 
            //This is something we need to change
            if (mydata.rd_en && edge_flag) begin
                
                word_register[count_burst - 4'd2] <= mydata.DQ;
                // if (count_burst > 4'd1) begin
                //     word_register[count_burst - 4'd2] <= mydata.DQ;
                // end
            end
        end
    end

    
    
    always_comb begin
        ncount_burst = count_burst;
        nDQS_t = DQS_t_2;

        if (count_burst >= 3'd2) begin
            nDQS_t = ~DQS_t_2;
        end
        if (mydata.wr_en || mydata.rd_en) begin
            ncount_burst = count_burst + 4'd1;        
        end 

        if (mydata.clear) begin
            ncount_burst = '0;
        end
    end
endmodule