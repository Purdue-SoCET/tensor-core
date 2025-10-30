`include "scpad_params.svh"
`include "scpad_pkg.sv"
`include "scpad_if.sv"
`include "swizzle_if.vh"
`include "dram_req_queue_if.vh"
`include "sram_write_latch_if.vh"
`include "dram_write_latch_if.vh"

/*  Julio Hernandez - herna628@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

module backend #(parameter logic [scpad_pkg::SCPAD_ID_WIDTH-1:0] IDX = '0) (
    scpad_if.backend_sched bshif, 
    scpad_if.backend_body bbif, 
    scpad_if.backend_dram bdrif
);
    import scpad_pkg::*;

    logic [5-1:0] be_id, uuid, nxt_uuid, schedule_request_counter, nxt_schedule_request_counter;
    logic [2:0] sub_uuid, nxt_sub_uuid, num_request;
    logic [DRAM_VECTOR_MASK-1:0] dram_vector_mask;
    logic nxt_sched_res_valid;
    logic initial_request_done, nxt_initial_request_done;
    

    always_ff @(posedge bshif.clk, negedge bshif.n_rst ) begin
        if(!bshif.n_rst) begin
            uuid <= 'b0;
            sub_uuid <= 'b0;
            bshif.sched_res[IDX].valid <= 'b0;
            schedule_request_counter <= 'b0;
            initial_request_done <= 1'b0;
        end else begin
            uuid <= nxt_uuid;
            sub_uuid <= nxt_sub_uuid;
            bshif.sched_res[IDX].valid <= nxt_sched_res_valid;
            schedule_request_counter <= nxt_schedule_request_counter;
            initial_request_done <= nxt_initial_request_done;
        end
    end

    swizzle_if baddr();
    dram_req_queue_if be_dr_req_q();
    sram_write_latch_if sr_wr_l();
    dram_write_latch_if dr_wr_l();

    swizzle swizzle_metadata(baddr);
    assign baddr.row_or_col = 1'b1; // Should always be 1'b1;
    assign baddr.spad_addr = {bshif.sched_req[IDX].spad_addr[19:5], 5'b00000}; // ignore lower 5 bits
    assign baddr.num_rows = bshif.sched_req[IDX].num_rows;
    assign baddr.num_cols = bshif.sched_req[IDX].num_cols;
    assign baddr.row_id = be_id;  // no matter which orientation we are in the      
    assign baddr.col_id = be_id;  // be_id keeps track
    // If sched_write == 1'b0 then it's a scpad load, so a dram read to a sram write.
    // This means the crossbar description we need is going to be based on the id that comes back from dram.

    // If sched write == 1'b1 then it's a scpad store, so a sram read to a dram write.
    // This mean the swizzle data we need can just come from our uuid.

    dram_request_queue dr_rd_req_q(bshif.clk, bshif.n_rst, be_dr_req_q);
    assign be_dr_req_q.sched_write = bshif.sched_req[IDX].write;
    assign be_dr_req_q.be_stall = bbif.be_stall[IDX];
    assign be_dr_req_q.num_request = num_request;
    assign be_dr_req_q.dram_be_stall = bdrif.dram_be_stall[IDX] || dr_wr_l.dram_write_latch_busy;
    assign be_dr_req_q.sched_valid = bshif.sched_req[IDX].valid;
    assign be_dr_req_q.initial_request_done = initial_request_done;
    // output dram_req, dram_queue_full, dram_req_latched

    sram_write_latch be_sr_wr_latch(bshif.clk, bshif.n_rst, sr_wr_l);
    assign sr_wr_l.dram_id = bdrif.dram_be_res[IDX].id;
    assign sr_wr_l.dram_res_valid = bdrif.dram_be_res[IDX].valid;
    assign sr_wr_l.spad_addr = {bshif.sched_req[IDX].spad_addr[19:5] + be_id, 5'b00000};
    assign sr_wr_l.xbar = baddr.xbar_desc;
    assign sr_wr_l.dram_rddata = bdrif.dram_be_res[IDX].rdata;
    assign sr_wr_l.num_request = num_request;
    assign sr_wr_l.be_stall = bbif.be_stall[IDX];
    // output sram_write_req, sram_write_req_latched

    dram_write_latch dr_wr_latch(bshif.clk, bshif.n_rst, dr_wr_l);
    assign dr_wr_l.dram_addr = {bshif.sched_req[IDX].dram_addr[DRAM_ADDR_WIDTH-1:5] + schedule_request_counter, 5'b00000};
    assign dr_wr_l.dram_vector_mask = dram_vector_mask;
    assign dr_wr_l.dram_valid = be_dr_req_q.dram_req.valid;
    assign dr_wr_l.dram_write = be_dr_req_q.dram_req.write;
    assign dr_wr_l.sram_rddata = be_dr_req_q.dram_req.wdata;
    assign dr_wr_l.num_request = num_request;
    assign dr_wr_l.be_stall = bbif.be_stall[IDX];
    assign dr_wr_l.dram_be_stall = bdrif.dram_be_stall[IDX];
    // output dram_write_req, dram_write_latch_busy, dram_write_req_latched

    always_comb begin
        num_request = 0;
        be_id = bdrif.dram_be_res[IDX].id[7:3];
        bbif.be_req[IDX].valid = 1'b0;
        bbif.be_req[IDX].write = 1'b0;
        bbif.be_req[IDX].addr = 0;
        bbif.be_req[IDX].num_rows = 0;
        bbif.be_req[IDX].num_cols = 0;
        bbif.be_req[IDX].row_id = 0;
        bbif.be_req[IDX].col_id = 0;
        bbif.be_req[IDX].row_or_col = 0;
        bbif.be_req[IDX].xbar = 0;
        bbif.be_req[IDX].wdata = 0;
        nxt_sched_res_valid = 1'b0;
        nxt_initial_request_done = initial_request_done; 
        
        
        if(bshif.sched_req[IDX].num_cols > 27) begin // need to determine num_packets so we can invalidate unneeded ones. Will always do 8 burst though
            num_request = 7;
        end else if(bshif.sched_req[IDX].num_cols > 23) begin
            num_request = 6;
        end else if(bshif.sched_req[IDX].num_cols > 19) begin
            num_request = 5;
        end else if(bshif.sched_req[IDX].num_cols > 15) begin
            num_request = 4;
        end else if(bshif.sched_req[IDX].num_cols > 11) begin
            num_request = 3;
        end else if(bshif.sched_req[IDX].num_cols > 7) begin
            num_request = 2;
        end else if(bshif.sched_req[IDX].num_cols > 3) begin
            num_request = 1;
        end

        if(bshif.sched_req[IDX].valid && (uuid == bshif.sched_req[IDX].num_rows) && (sub_uuid == num_request)) begin
            nxt_initial_request_done = 1'b1; 
        end

        nxt_sub_uuid = sub_uuid;
        nxt_uuid = uuid;
        dram_vector_mask = 4'b1111; // dram_vector_mask can be a static 8 bytes unless you want to get rid of padding
        
        // sched_write == 1'b0  scpad load, dram read to a sram write.
        if(bshif.sched_req[IDX].num_cols == 5'b11111) begin
            be_dr_req_q.dram_addr = ({bshif.sched_req[IDX].dram_addr[DRAM_ADDR_WIDTH-1:5] + uuid, sub_uuid, 2'b00});
        end else begin 
            be_dr_req_q.dram_addr = ({bshif.sched_req[IDX].dram_addr[DRAM_ADDR_WIDTH-1:5], sub_uuid, 2'b00}) + uuid * (bshif.sched_req[IDX].num_cols + 1);
        end
        be_dr_req_q.id = uuid;
        be_dr_req_q.sub_id = sub_uuid;


        
        be_dr_req_q.sram_rdata = bbif.be_res[IDX].rdata;
        be_dr_req_q.sram_res_valid = bbif.be_res[IDX].valid;
        

        if(sub_uuid == num_request) begin  // if you want to add exactly the amount of dram_vector_mask with no padding
            if((bshif.sched_req[IDX].num_cols[1:0] & 2'b11) == 2'b00) begin
                dram_vector_mask = 4'b0001;
            end else if((bshif.sched_req[IDX].num_cols[1:0] & 2'b11) == 2'b01) begin
                dram_vector_mask = 4'b0011;
            end else if((bshif.sched_req[IDX].num_cols[1:0] & 2'b11) == 2'b10) begin
                dram_vector_mask = 4'b0111;
            end
        end

        be_dr_req_q.dram_vector_mask = dram_vector_mask;

        if(be_dr_req_q.burst_complete == 1'b1) begin
            nxt_sub_uuid = sub_uuid + 1;
            if(sub_uuid == num_request) begin
                nxt_sub_uuid = 0;
                nxt_uuid = uuid + 1;
            end
        end

        nxt_schedule_request_counter = schedule_request_counter;

        if(sr_wr_l.sram_write_req_latched == 1'b1) begin // be_stall is checked in sram latch 
            bbif.be_req[IDX].valid = sr_wr_l.sram_write_req.valid;
            bbif.be_req[IDX].write = 1'b1;
            bbif.be_req[IDX].addr = sr_wr_l.sram_write_req.spad_addr;
            bbif.be_req[IDX].wdata = sr_wr_l.sram_write_req.wdata;
            bbif.be_req[IDX].xbar = sr_wr_l.sram_write_req.xbar;
            nxt_schedule_request_counter = schedule_request_counter + 1;
        end

        bdrif.be_dram_req[IDX].valid = be_dr_req_q.dram_req.valid;
        bdrif.be_dram_req[IDX].write = 1'b0;
        bdrif.be_dram_req[IDX].id = be_dr_req_q.dram_req.id;
        bdrif.be_dram_req[IDX].dram_addr = be_dr_req_q.dram_req.dram_addr;
        bdrif.be_dram_req[IDX].dram_vector_mask = be_dr_req_q.dram_req.dram_vector_mask;
        bdrif.be_dram_req[IDX].wdata = 0;
        bdrif.be_dram_stall[IDX] = bbif.be_stall[IDX];

        if(bshif.sched_req[IDX].write == 1'b1) begin // sched write == 1'b1, scpad store, sram read to a dram write.
            be_id = uuid;
            
            if(bbif.be_stall[IDX] == 1'b0) begin
                bbif.be_req[IDX].valid = 1'b1 && !initial_request_done;
                bbif.be_req[IDX].write = 1'b0;
                bbif.be_req[IDX].addr = {bshif.sched_req[IDX].spad_addr[19:5] + uuid, 5'b00000};
                bbif.be_req[IDX].num_rows = bshif.sched_req[IDX].num_rows;
                bbif.be_req[IDX].num_cols = bshif.sched_req[IDX].num_cols;
                bbif.be_req[IDX].row_id = uuid;
                bbif.be_req[IDX].col_id = uuid;
                bbif.be_req[IDX].row_or_col = 1'b1;
                bbif.be_req[IDX].xbar = baddr.xbar_desc;
                bbif.be_req[IDX].wdata = 0;
                nxt_uuid = initial_request_done ? uuid : uuid + 1;
            end

            if(dr_wr_l.dram_write_req_latched == 1'b1) begin
                nxt_sub_uuid = sub_uuid + 1;
                if(sub_uuid == num_request) begin
                    nxt_sub_uuid = 0;
                    nxt_schedule_request_counter = schedule_request_counter + 1;
                end
            end

            bdrif.be_dram_req[IDX].valid = dr_wr_l.dram_write_req.valid;
            bdrif.be_dram_req[IDX].write = dr_wr_l.dram_write_req.valid;
            bdrif.be_dram_req[IDX].id = 0; // doesn't matter it's just a write
            bdrif.be_dram_req[IDX].dram_addr = dr_wr_l.dram_write_req.dram_addr;
            bdrif.be_dram_req[IDX].dram_vector_mask = dr_wr_l.dram_write_req.dram_vector_mask;
            bdrif.be_dram_req[IDX].wdata = dr_wr_l.dram_write_req.wdata;
            bdrif.be_dram_stall[IDX] = 0; // backend won't have to stall dram in a scpad store. This is because there are no hazards created in backend that would necessitate pausing dram writes.

        end

        if(bshif.sched_req[IDX].valid && (schedule_request_counter == bshif.sched_req[IDX].num_rows) && ((dr_wr_l.dram_write_req_latched == 1'b1) || (sr_wr_l.sram_write_req_latched == 1'b1))) begin
            nxt_sched_res_valid = 1'b1;
            nxt_uuid = 0;
            nxt_sub_uuid = 0;
            nxt_schedule_request_counter = 0;
            nxt_initial_request_done = 0;
        end
        
    end

endmodule