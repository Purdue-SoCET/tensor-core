`include "scpad_pkg.sv"
`include "scpad_if.sv"
`include "dram_write_latch_if.vh"

/*  Julio Hernandez - herna628@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

    // modport dram_write_latch (
    //     input dram_addr, num_bytes, dram_valid, dram_write, sram_rddata, num_request,
    //     input be_stall,
    //     output dram_write_req, dram_write_latch_busy, dram_write_req_latched
    // );

module dram_write_latch ( // UUID now needs to have 2 lower bits for an offest since dram can only handle 64 bits at a time
    input logic clk, n_rst, 
    dram_write_latch_if.dram_write_latch dr_wr_l
);
    import scpad_pkg::*;

    // typedef struct packed {
    //     logic valid; 
    //     logic [63:0] wdata;
    //     logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //     logic [COL_IDX_WIDTH-1:0]   num_bytes;
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

        if(dr_wr_l.dram_be_busy == 1'b0) begin
            if(dr_wr_l.dram_write == 1'b1 && dr_wr_l.dram_valid == 1'b1 && request_completed_counter != dr_wr_l.num_request) begin
                dr_wr_l.dram_write_latch_busy = 1'b1;
                nxt_dram_write_latch.valid = 1'b1;
                if(request_completed_counter[2:0] == 3'b000) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[63:0];
                end else if(request_completed_counter[2:0] == 3'b001) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[127:64];
                end else if(request_completed_counter[2:0] == 3'b010) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[191:128];
                end else if(request_completed_counter[2:0] == 3'b011) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[255:192];
                end else if(request_completed_counter[2:0] == 3'b100) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[319:256];
                end else if(request_completed_counter[2:0] == 3'b101) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[383:320];
                end else if(request_completed_counter[2:0] == 3'b110) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[447:384];
                end else if(request_completed_counter[2:0] == 3'b111) begin
                    nxt_dram_write_latch.wdata = dr_wr_l.sram_rddata[512:448];
                end
                nxt_dram_write_latch.dram_addr = {dr_wr_l.dram_addr[DRAM_ADDR_WIDTH-1:5], request_completed_counter[2:0], 2'b00};
                nxt_dram_write_latch.num_bytes = dr_wr_l.num_bytes;
                nxt_request_completed_counter = request_completed_counter + 1;
            end

            if(dram_write_latch.valid == 1'b1) begin
                dr_wr_l.dram_write_req = dram_write_latch;
            end

            if(request_completed_counter == dr_wr_l.num_request) begin
                dr_wr_l.dram_write_latch_busy = 1'b0;
                dr_wr_l.dram_write_req_latched = 1'b1;
                nxt_request_completed_counter = 0;
                nxt_dram_write_latch = 0;
            end
        end
        
    end

endmodule
