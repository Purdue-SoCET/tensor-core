`include "scpad_pkg.sv"
`include "scpad_if.sv"
`include "sram_write_latch_if.vh"

    // modport sram_write_latch (
    //     input dram_id, dram_res_valid, xbar, dram_rddata, num_request,
    //     input be_stall,
    //     output sram_write_req, sram_write_req_latched
    // );


module dram_request_queue ( // UUID now needs to have 2 lower bits for an offest since dram can only handle 64 bits at a time
    input logic clk, n_rst, 
    sram_write_latch_if.sram_write_latch sr_wr_l
);
    import scpad_pkg::*;

    // typedef struct packed {
    //     logic valid; 
    //     scpad_data_t wdata;
    //     xbar_desc_t xbar;
    // } sram_write_req_t;

    sram_write_req_t sram_write_latch;
    sram_write_req_t nxt_sram_write_latch;

    logic [2:0] request_completed_counter, nxt_request_completed_counter; // max request is 8
    
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            sram_write_latch <= 'b0;
            request_completed_counter <= 'b0;
        end else begin
            sram_write_latch <= nxt_sram_write_latch;
            request_completed_counter <= nxt_request_completed_counter;
        end
    end

    always_comb begin
        nxt_sram_write_latch = sram_write_latch;
        nxt_request_completed_counter = request_completed_counter;
        sr_wr_l.sram_write_req = 0;
        sr_wr_l.sram_write_req_latched = 1'b0;

        if(sr_wr_l.dram_res_valid) begin
            nxt_sram_write_latch.valid = ((request_completed_counter + 1) == sr_wr_l.num_request) ? 1'b1 : 1'b0;
            if(sr_wr_l.dram_id[2:0] == 3'b000) begin
                nxt_sram_write_latch.wdata[3:0] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b001) begin
                nxt_sram_write_latch.wdata[7:4] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b010) begin
                nxt_sram_write_latch.wdata[11:8] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b011) begin
                nxt_sram_write_latch.wdata[15:12] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b100) begin
                nxt_sram_write_latch.wdata[19:16] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b101) begin
                nxt_sram_write_latch.wdata[23:20] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b110) begin
                nxt_sram_write_latch.wdata[27:24] =  sr_wr_l.dram_rddata;
            end else if(sr_wr_l.dram_id[2:0] == 3'b111) begin
                nxt_sram_write_latch.wdata[31:28] =  sr_wr_l.dram_rddata;
            end
            nxt_sram_write_latch.xbar = sr_wr_l.xbar;
            nxt_request_completed_counter = request_completed_counter + 1;
        end

        if((sr_wr_l.be_stall == 1'b0) && (sram_write_latch.valid == 1'b1)) begin
            sr_wr_l.sram_write_req = sram_write_latch;
            nxt_sram_write_latch = 0;
            sr_wr_l.sram_write_req_latched = 1'b1;
            nxt_request_completed_counter = 0;
        end

        
    end

endmodule
