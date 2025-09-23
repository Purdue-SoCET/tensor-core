`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module sram_cntrl (
    input  logic clk, n_rst,
    scpad_if.top srif,

    output logic [NUM_COLS-1:0] ren [NUM_SCPADS],
    output logic [NUM_COLS-1:0] wen  [NUM_SCPADS],
    input  logic [NUM_COLS-1:0] rdone [NUM_SCPADS],
    input logic [NUM_COLS-1:0] wdone [NUM_SCPADS],

    output logic [ROW_IDX_WIDTH-1:0] raddr [NUM_SCPADS],
    output logic [ROW_IDX_WIDTH-1:0] waddr [NUM_SCPADS],

    input logic [NUM_COLS-1:0][DATA_W-1:0] sram_banks_read_vector  [NUM_SCPADS][NUM_COLS],
    output logic  [NUM_COLS-1:0][DATA_W-1:0] sram_banks_write_vector [NUM_SCPADS][NUM_COLS]
);
    import scpad_types_pkg::*;

    typedef sram_r_req_t multi_bank_req_t [NUM_SCPADS]; 

    logic conflict [NUM_SCPADS];
    logic stall_pipe [NUM_SCPADS];
    logic [NUM_COLS-1:0] bank_conflicts [NUM_SCPADS]; 

    logic pipe_ahead;
    assign pipe_ahead = 1'b1; 


    /////////////////////////////// Do we ever consider this?  ///////////////////////////////

    always_comb begin
        bank_conflicts = '0;
        for (int j = 0; j < NUM_SCPADS; j++) begin 
            for (int i = 0; i < NUM_COLS; i++) begin
                bank_conflicts[j][i] = (srif.sram_read_req.valid & srif.sram_write_req.valid) & 
                (srif.sram_read_req.enable_mask[i] & srif.sram_write_req.enable_mask[i]) & 
                (srif.sram_read_req.slot_mask[i] == srif.sram_write_req.slot_mask[i]);
            end
        end 
    end

    assign conflict[0] = |bank_conflicts[0]; 
    assign conflict[1] = |bank_conflicts[1]; 


    //////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////// Issue Pipe /////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////////

    sram_r_req_t tmp_read; 
    sram_w_req_t tmp_write; 

    latch #(.T(sram_r_req_t)) top_l1 (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(sif.sram_write_req), .out(tmp_read)
    ); 
    latch #(.T(sram_w_req_t)) top_l2 (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(sif.sram_read_req), .out(tmp_write)
    ); 

    /////////////////////////////// ARB Logic ///////////////////////////////

    logic both_valid_same_spad;
    logic grant_r, grant_w;
    multi_bank_req_t r1, w1, r2, w2;

    assign both_valid_same_spad = tmp_r.valid & tmp_w.valid & (tmp_r.scpad_id == tmp_w.scpad_id);
    assign grant_r = (both_valid_same_spad) ? tmp_r.valid : 1'b0;
    assign grant_w = (both_valid_same_spad) ? tmp_w.valid : 1'b1;

    always_comb begin
        r1 = '0;
        w1 = '0;

        if (grant_r) r1[tmp_read.scpad_id] = tmp_read;
        if (grant_w) w1[tmp_write.scpad_id] = tmp_write;
    end

    latch #(.T(multi_bank_req_t)) top_l1 (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(r1), .out(r2)
    ); 
    latch #(.T(multi_bank_req_t)) top_l1 (.clk(clk), .n_rst(n_rst), 
        .en(pipe_ahead), .in(w1), .out(w2)
    ); 

    ////////////////////////  Set the SRAM Bank Signals for R/W ///////////////////////////////

    inflight_tag_t r_tag, w_tag; 

    always_comb begin
        ren = '0;
        wen = '0;
        raddr = '0;
        waddr = '0;
        sram_banks_write_vector = '0;

        for (int s = 0; s < NUM_SCPADS; s++) begin
            if (r1[s].valid) begin
                ren[s] = r2[s].xbar_desc.enable_mask;
                raddr[s] = r2[s].xbar_desc.slot_mask; 
            end
            if (r2[s].valid) begin
                wen[s] = w2[s].xbar_desc.enable_mask;
                waddr[s] = w2[s].xbar_desc.slot_mask;
                sram_banks_write_vector[s] = w2[s].wdata; 
            end
        end
    end

    always_ff @(posedge clk, negedge n_rst) begin
        if (!n_rst) begin
            r_tag <= '0;
            w_tag <= '0;
        end else begin
            for (int s = 0; s < NUM_SCPADS; s++) begin
                if (r1[s].valid && !r_tag[s].valid) begin
                    r_tag[s].valid <= 1'b1;
                    r_tag[s].int_id <= r1[s].int_id;
                    r_tag[s].mask <= r1[s].xbar_desc.enable_mask;
                end
                else if (read_done_spad[s]) begin // Clear to fill slot for next issue
                    r_tag[s].valid <= 1'b0;
                end

                if (w1_to_spad[s].valid && !w_tag[s].valid) begin
                    w_tag[s].valid <= 1'b1;
                    w_tag[s].int_id <= w1_to_spad[s].int_id;
                    w_tag[s].mask <= w1_to_spad[s].xbar_desc.enable_mask;
                end
                else if (write_done_spad[s]) begin // Clear to fill slot for next issue
                    w_tag[s].valid <= 1'b0;
                end
            end
        end
    end


    //////////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////// Response Pipe /////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////////


    /////////////////////////////// POST SRAM Banks - Read ///////////////////////////////

    logic read_done_spad [NUM_SCPADS];
    logic any_r_done;
    logic [$clog2(NUM_SCPADS)-1:0] r_done_idx;
    sram_r_res_t rres_next;

    always_comb begin
        any_r_done  = 1'b0;
        r_done_idx  = '0;
        rres_next = '0;

        for (int s = 0; s < NUM_SCPADS; s++) begin
            read_done_spad[s] = r_tag[s].valid & (|(rdone[s] & r_tag[s].mask));
            if (read_done_spad[s] && !any_r_done) begin
                any_r_done = 1'b1;
                r_done_idx = s[$clog2(NUM_SCPADS)-1:0];
            end
        end

        if (any_r_done) begin
            rres_next.valid  = 1'b1;
            rres_next.int_id = r_tag[r_done_idx].int_id;

            for (int b=0; b<NUM_COLS; b++) begin
                rres_next.rdata[b] = r_tag[r_done_idx].mask[b] ? sram_banks_read_vector[r_done_idx][b] : '0;
            end
        end
    end

    always_ff @(posedge clk, negedge n_rst) begin
        if (!n_rst) begin
            srif.sram_read_res <= '0;
        end else begin
            srif.sram_read_res <= rres_next;
            if (any_r_done) r_tag[r_done_idx].valid <= 1'b0; 
        end
    end


    /////////////////////////////// POST SRAM Banks - Write ///////////////////////////////

    logic any_w_done;
    logic write_done_spad [NUM_SCPADS];
    logic [$clog2(NUM_SCPADS)-1:0] w_done_idx;
    sram_w_res_t wres_next;

    always_comb begin
        any_w_done = 1'b0;
        w_done_idx = '0;
        wres_next = '0;

        for (int s = 0; s < NUM_SCPADS; s++) begin
            write_done_spad[s] = w_tag[s].valid & ( | ( wdone[s] & w_tag[s].mask ) );
            if (write_done_spad[s] && !any_w_done) begin
                any_w_done = 1'b1;
                w_done_idx = s[$clog2(NUM_SCPADS)-1:0];
            end
        end

        if (any_w_done) begin
            wres_next.valid  = 1'b1;
            wres_next.int_id = w_tag[w_done_idx].int_id;
        end
    end


    always_ff @(posedge clk, negedge n_rst) begin
        if (!n_rst) begin
            srif.sram_write_res <= '0;
        end else begin
            srif.sram_write_res <= wres_next;
            if (any_w_done) w_tag[w_done_idx].valid <= 1'b0;
        end
    end

endmodule