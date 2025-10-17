`include "scpad_pkg.sv"
`include "scpad_if.sv"
import scpad_pkg::*;

module frontend #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.frontend_vec fvif, scpad_if.frontend_body fsif); 
    //pipeline enable
    logic pipe_EN;
    assign pipe_EN = !fsif.fe_stall[IDX];

    // vec stall = body stall
    assign fvif.fe_vec_stall[IDX] = fsif.fe_stall[IDX];

    // latch incoming request from vc
    // only latch when req valid and pipeline en

    //intermediate edited request
    req_t vec_req0;

    latch #(.T(req_t)) u_latch_vec_req (
        .clk(fvif.clk),
        .n_rst(fvif.n_rst),
        .en(pipe_EN),
        .in(fvif.vec_req[IDX]),
        .out(vec_req0)
    );

    //generating masks & edited request
    mask_t valid_mask_gen;
    shift_mask_t shift_mask_gen;
    slot_mask_t slot_mask_gen;

    //getting base row
    logic [ROW_IDX_WIDTH-1:0] row_idx;
    logic [COL_IDX_WIDTH-1:0] col_idx;
    addr_to_row_col(vec_req0.addr, row_idx, col_idx);

    // instantiate mask generator
    swizzle u_swizzle (
        .row_or_col(vec_req0.row_or_col),
        .base_row(row_idx),
        .row_id(vec_req0.row_id),
        .col_id(vec_req0.col_id),
        .rows(vec_req0.num_rows),
        .cols(vec_req0.num_cols),

        .valid_mask(valid_mask_gen),
        .shift_mask(shift_mask_gen),
        .slot_mask(slot_mask_gen)
    );

    //edited request bundling
    req_t vec_req1;
    always_comb begin
        vec_req1 = vec_req0;
        vec_req1.xbar.valid_mask = valid_mask_gen;
        vec_req1.xbar.shift_mask = shift_mask_gen;
        vec_req1.xbar.slot_mask = slot_mask_gen;
    end

    //latch edited requests
    latch #(.T(req_t)) u_latch_sram_req (
        .clk(fvif.clk),
        .n_rst(fvif.n_rst),
        .en(pipe_EN),
        .in(vec_req1),
        .out(fsif.fe_req[IDX])
    );

    ///sent to body

    // latch response from Body back to Vector Core
    latch #(.T(res_t)) u_latch_sram_res (
        .clk(fvif.clk),
        .n_rst(fvif.n_rst),
        .en(pipe_EN),
        .in(fsif.fe_res[IDX]),
        .out(fvif.vec_res[IDX])
    );

endmodule