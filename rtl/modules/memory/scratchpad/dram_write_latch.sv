`include "scpad_pkg.sv"
`include "scpad_if.sv"
`include "dram_write_latch_if.vh"

/*  Julio Hernandez - herna628@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

    // modport dram_write_latch (
    //     input dram_addr, dram_vector_mask, dram_valid, dram_write, sram_rddata, num_request,
    //     input be_stall,
    //     output dram_write_req, dram_write_latch_busy, dram_write_req_latched
    // );

module dram_write_latch ( // UUID now needs to have 3 lower bits for an offest since dram can only handle 64 bits at a time
    input logic clk, n_rst, 
    dram_write_latch_if.dram_write_latch dr_wr_l
);
    import scpad_pkg::*;

    // typedef struct packed {
    //     logic valid; 
    //     logic [63:0] wdata;
    //     logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //     logic [COL_IDX_WIDTH-1:0]   dram_vector_mask;
    // } dram_write_req_t;

    dram_write_req_t dram_write_latch,  nxt_dram_write_latch;

    logic [3:0] request_completed_counter, nxt_request_completed_counter; // max completed request is 8
    
    always_ff @(posedge clk, negedge n_rst) begin
        if(!n_rst) begin
            dram_write_latch <= 'b0;
            request_completed_counter <= 'b0;
        end else begin
            dram_write_latch <= nxt_dram_write_latch;
            request_completed_counter <= nxt_request_completed_counter;
        end
    end

    always_comb begin
        nxt_request_completed_counter = request_completed_counter;
        dr_wr_l.dram_write_latch_busy = 1'b0;
        dr_wr_l.dram_write_req_latched = 1'b0;
        nxt_dram_write_latch = dram_write_latch;

        if(dr_wr_l.dram_be_stall == 1'b0) begin
            if(dr_wr_l.dram_write == 1'b1 && dr_wr_l.dram_valid == 1'b1 && request_completed_counter != dr_wr_l.num_request) begin
                dr_wr_l.dram_write_latch_busy = 1'b1;
                nxt_dram_write_latch.valid = 1'b1;
                if(request_completed_counter[2:0] == 3'b000) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[3][15:0], dr_wr_l.sram_rddata[2][15:0], dr_wr_l.sram_rddata[1][15:0], dr_wr_l.sram_rddata[0][15:0]};
                end else if(request_completed_counter[2:0] == 3'b001) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[7][15:0], dr_wr_l.sram_rddata[6][15:0], dr_wr_l.sram_rddata[5][15:0], dr_wr_l.sram_rddata[4][15:0]};
                end else if(request_completed_counter[2:0] == 3'b010) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[11][15:0], dr_wr_l.sram_rddata[10][15:0], dr_wr_l.sram_rddata[9][15:0], dr_wr_l.sram_rddata[8][15:0]};
                end else if(request_completed_counter[2:0] == 3'b011) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[15][15:0], dr_wr_l.sram_rddata[14][15:0], dr_wr_l.sram_rddata[13][15:0], dr_wr_l.sram_rddata[12][15:0]};
                end else if(request_completed_counter[2:0] == 3'b100) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[19][15:0], dr_wr_l.sram_rddata[18][15:0], dr_wr_l.sram_rddata[17][15:0], dr_wr_l.sram_rddata[16][15:0]};
                end else if(request_completed_counter[2:0] == 3'b101) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[23][15:0], dr_wr_l.sram_rddata[22][15:0], dr_wr_l.sram_rddata[21][15:0], dr_wr_l.sram_rddata[20][15:0]};
                end else if(request_completed_counter[2:0] == 3'b110) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[27][15:0], dr_wr_l.sram_rddata[26][15:0], dr_wr_l.sram_rddata[25][15:0], dr_wr_l.sram_rddata[24][15:0]};
                end else if(request_completed_counter[2:0] == 3'b111) begin
                    nxt_dram_write_latch.wdata = {dr_wr_l.sram_rddata[31][15:0], dr_wr_l.sram_rddata[30][15:0], dr_wr_l.sram_rddata[29][15:0], dr_wr_l.sram_rddata[28][15:0]};
                end
                nxt_dram_write_latch.dram_addr = {dr_wr_l.dram_addr[DRAM_ADDR_WIDTH-1:5], request_completed_counter[2:0], 2'b00};
                nxt_dram_write_latch.dram_vector_mask = dr_wr_l.dram_vector_mask;
                nxt_request_completed_counter = request_completed_counter + 1;
            end

            if(dram_write_latch.valid == 1'b1) begin
                dr_wr_l.dram_write_req = dram_write_latch;
                if(request_completed_counter == dr_wr_l.num_request) begin
                    dr_wr_l.dram_write_latch_busy = 1'b0;
                    dr_wr_l.dram_write_req_latched = 1'b1;
                    nxt_request_completed_counter = 0;
                    nxt_dram_write_latch = 0;
                end
            end

            
        end
        
    end

endmodule