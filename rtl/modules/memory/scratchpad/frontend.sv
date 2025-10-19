/*  Nicha Muninnimit - nmuninni@purdue.edu */
/*  Rafael Monteiro Martins Pinheiro - rmontei@purdue.edu */
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

`include "scpad_pkg.sv"
`include "scpad_if.sv"
import scpad_pkg::*;

module frontend #(parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0) (scpad_if.frontend_vec fvif, scpad_if.frontend_body fsif); 

    logic [ROW_IDX_WIDTH-1:0] row_idx;
    logic [COL_IDX_WIDTH-1:0] col_idx;

    // Propagate downstream stalls    
    assign fvif.fe_vec_stall[IDX] = fsif.fe_stall[IDX];

    generate 
        if (LATCH_INT) begin 
            latch #(.T(req_t)) u_latch_vec_req (
                .clk(fvif.clk),
                .n_rst(fvif.n_rst),
                .en(!fsif.fe_stall[IDX]),
                .in(fvif.vec_req[IDX]),
                .out(fsif.fe_req[IDX])
            );
            latch #(.T(res_t)) u_latch_vec_res (
                .clk(fsif.clk),
                .n_rst(fsif.n_rst),
                .en(1'b1),
                .in(fsif.fe_res[IDX]),
                .out(fvif.vec_res[IDX])
            );
        end else begin 
            assign fsif.fe_req[IDX] = fvif.vec_req[IDX];
            assign fvif.vec_res[IDX] = fsif.fe_res[IDX]; 
        end 
    endgenerate

    addr_to_row_col(fsif.fe_req[IDX].addr, row_idx, col_idx);

    // Swizzle Desc
    swizzle u_swizzle (
        .row_or_col(fsif.fe_req[IDX].row_or_col),
        .base_row(row_idx),
        .row_id(fsif.fe_req[IDX].row_id),
        .col_id(fsif.fe_req[IDX].col_id),
        .rows(fsif.fe_req[IDX].num_rows),
        .cols(fsif.fe_req[IDX].num_cols),

        .valid_mask(fsif.fe_req[IDX].xbar.valid_mask),
        .shift_mask(fsif.fe_req[IDX].xbar.shift_mask),
        .slot_mask(fsif.fe_req[IDX].xbar.slot_mask)
    );

endmodule