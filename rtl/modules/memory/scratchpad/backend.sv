`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"
`include "swizzle_if.vh"
`include "dram_req_queue_if.vh"
`include "sram_write_latch_if.vh"
`include "dram_write_latch_if.vh"

module backend #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) // grab clk and n_rst from any
    (   input clk, n_rst, 
        scpad_if.backend_sched bshif, 
        scpad_if.backend_scpads bscif, 
        scpad_if.backend_dram bdrif
); 

logic [DRAM_ID_WIDTH-1:0] uuid, nxt_uuid;
logic [2:0] sub_uuid, nxt_sub_uuid, num_request; 
logic [2:0] num_bytes;

always_ff @(posedge clk, negedge n_rst ) begin
    if(!n_rst) begin
        uuid <= 'b0;
        sub_uuid <= 'b0;
    end else begin
        uuid <= nxt_uuid;
        sub_uuid <= nxt_sub_uuid;
    end
end

addr_map_if baddr();
dram_req_queue_if be_dr_req_q();
sram_write_latch_if sr_wr_l();
dram_write_latch_if dr_wr_l();

addr_map swizzle_metadata(baddr);
assign baddr.row_or_col = bshif.sched_req.row_or_col;
assign baddr.spad_addr = {bshif.sched_req.spad_addr[19:5], 5'b00000}; // ignore lower 5 bits
assign baddr.num_rows = bshif.sched_req.num_rows;
assign baddr.num_cols = bshif.sched_req.num_cols;
assign baddr.row_id = be_id;  // no matter which orientation we are in the      
assign baddr.col_id = be_id;  // be_id keeps track
// If sched_write == 1'b0 then it's a scpad load, so a dram read to a sram write.
// This means the crossbar description we need is going to be based on the id that comes back from dram.

// If sched write == 1'b1 then it's a scpad store, so a sram read to a dram write.
// This mean the swizzle data we need can just come from our uuid.

dram_request_queue dr_rd_req_q(clk, n_rst, be_dr_req_q);
assign be_dr_rd_req_q.sched_write = bshif.sched_req.write;
assign be_dr_rd_req_q.be_stall = bscif.be_stall;
assign be_dr_rd_req_q.dram_be_stall = bdrif.dram_be_stall || dr_wr_l.dram_write_latch_busy;
// output dram_req, dram_queue_full, dram_req_latched

sram_write_latch be_sr_wr_latch(clk, n_rst, sr_wr_l);
assign sr_wr_l.dram_id = bdrif.dram_be_res.id;
assign sr_wr_l.dram_res_valid = bdrif.dram_be_res.valid;
assign sr_wr_l.xbar = baddr.xbar_desc;
assign sr_wr_l.dram_rddata = bdrif.dram_be_res.rdata;
assign sr_wr_l.num_request = num_request;
assign sr_wr_l.be_stall = bscif.be_stall;
// output sram_write_req, sram_write_req_latched

dram_write_latch dr_wr_latch(clk,n_rst, dr_wr_l);
assign dr_wr_l.dram_addr = {bscif.sched_req.dram_addr[DRAM_ADDR_WIDTH-1:5] + uuid, 5'b00000};
assign dr_wr_l.num_bytes = num_bytes;
assign dr_wr_l.dram_valid = be_dr_rd_req_q.dram_req.valid;
assign dr_wr_l.dram_write = be_dr_rd_req_q.dram_req.write;
assign dr_wr_l.sram_rddata = be_dr_rd_req_q.dram_req.wdata;
assign dr_wr_l.num_request = num_request;
assign dr_wr_l.be_stall = bscif.be_stall;
// output dram_write_req, dram_write_latch_busy, dram_write_req_latched

always_comb begin
    num_request = 1;
    be_id = bdrif.dram_be_res.id[7:3];

    if(bshif.sched_req.num_cols > 28) begin // need to determine num_packets so we can invalidate unneeded ones. Will always do 8 burst though
        num_request = 8;
    end else if(bshif.sched_req.num_cols > 24) begin
        num_request = 7;
    end else if(bshif.sched_req.num_cols > 20) begin
        num_request = 6;
    end else if(bshif.sched_req.num_cols > 16) begin
        num_request = 5;
    end else if(bshif.sched_req.num_cols > 12) begin
        num_request = 4;
    end else if(bshif.sched_req.num_cols > 8) begin
        num_request = 3;
    end else if(bshif.sched_req.num_cols > 4) begin
        num_request = 2;
    end

    nxt_sub_uuid = sub_uuid;
    nxt_uuid = uuid;
    nxt_sched_res_valid = 1'b0;
    num_bytes = 8; // num_bytes can be a static 8 bytes unless you want to get rid of padding
    
    // sched_write == 1'b0 dram read to a sram write.
    be_dr_rd_req_q.dram_addr = {bscif.sched_req.dram_addr[DRAM_ADDR_WIDTH-1:5] + uuid, sub_uuid, 2'b00};
    be_dr_rd_req_q.id = uuid;
    be_dr_rd_req_q.sub_id = sub_uuid;
    
    be_dr_rd_req_q.sram_rdata = 0;
    be_dr_rd_req_q.sram_res_valid = 0;

    // if(sub_uuid + 1 == num_request) begin                // if you want to add exactly the amount of num_bytes with no padding
    //     if(bshif.sched_req.num_cols % 4 == 1) begin      // will also need to change dram_addr calculations.
    //         num_bytes = 2;
    //     end else if(bshif.sched_req.num_cols % 4 == 2) begin
    //         num_bytes = 4;
    //     end else if(bshif.sched_req.num_cols % 4 == 3) begin
    //         num_bytes = 6;
    //     end
    // end

    be_dr_rd_req_q.num_bytes = num_bytes;

    if(be_dr_rd_req_q.burst_complete == 1'b1) begin
        nxt_sub_uuid = sub_uuid + 1;
        if(sub_uuid == num_request) begin
            nxt_sub_uuid = 0;
        end
    end

    if(be_dr_rd_req_q.transaction_complete == 1'b1) begin
        nxt_uuid = uuid + 1;
        if(uuid == bscif.sched_req.num_rows) begin
            nxt_uuid = 0;
        end
    end

    if(sr_wr_l.sram_write_req_latched == 1'b1) begin // be_stall is checked in sram latch 
        bscif.be_req = sr_wr_l.sram_write_req;
    end

    bdrif.be_dram_req.valid = be_dr_rd_req_q.dram_req.valid;
    bdrif.be_dram_req.write = 1'b0;
    bdrif.be_dram_req.id = be_dr_rd_req_q.dram_req.id;
    bdrif.be_dram_req.dram_addr = be_dr_rd_req_q.dram_req.dram_addr;
    bdrif.be_dram_req.num_bytes = be_dr_rd_req_q.dram_req.num_bytes;
    bdrif.be_dram_req.wdata = 0;
    

    // typedef struct packed {
    //     logic valid; 
    //     logic write;
    //     logic [DRAM_ID_WIDTH-1:0]   id;
    //     logic [DRAM_ADDR_WIDTH-1:0] dram_addr;
    //     logic [COL_IDX_WIDTH-1:0]   num_bytes;
    //     scpad_data_t wdata;
    // } dram_req_t;

    if(bshif.sched_req.write; == 1'b1) begin // sched write == 1'b1 then sram read to a dram write.
        be_id = uuid;
        if(bscif.be_stall == 1'b0) begin
            bscif.be_req.valid = 1'b1;
            bscif.be_req.write = 1'b0;
            /* needed?
            bscif.be_req.addr = {bshif.sched_req.spad_addr[19:5] + uuid, 5'b00000};
            bscif.be_req.num_rows = 0;
            bscif.be_req.num_cols = 0;
            bscif.be_req.row_id = 0;
            bscif.be_req.col_id = 0;
            */
            bscif.be_req.row_or_col = bshif.sched_req.row_or_col;
            bscif.be_req.xbar = baddr.xbar_desc;
            bscif.be_req.wdata = 0;
        end

        bdrif.be_dram_req.valid = dr_wr_l.dram_write_latch.valid;
        bdrif.be_dram_req.write = dr_wr_l.dram_write_latch.valid;
        bdrif.be_dram_req.id = 0; // doesn't matter it's just a write
        bdrif.be_dram_req.dram_addr = dr_wr_l.dram_write_latch.dram_addr;
        bdrif.be_dram_req.num_bytes = dr_wr_l.dram_write_latch.num_bytes;
        bdrif.be_dram_req.wdata = dr_wr_l.dram_write_latch.wdata;    
    end
    
end



endmodule