`include "swizzle_if.vh"
/*  Akshath Raghav Ravikiran - araviki@purdue.edu */

module swizzle (
  swizzle_if.swizzle swizz
);

    import scpad_pkg::*;

    logic [ROW_IDX_WIDTH-1:0] abs_row;

    always_comb begin
        swizz.xbar_desc.valid_mask = '0;
        swizz.xbar_desc.shift_mask = '0;
        swizz.xbar_desc.slot_mask  = '0;

        for (int bank_id = 0; bank_id < NUM_COLS; bank_id++) begin
            if (swizz.row_or_col) begin // row-major read
                abs_row = swizz.spad_addr + swizz.row_id;
                swizz.xbar_desc.valid_mask[bank_id] = (bank_id < swizz.num_cols);
                swizz.xbar_desc.shift_mask[bank_id] = COL_IDX_WIDTH'((bank_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
                swizz.xbar_desc.slot_mask[bank_id]  = abs_row;
            end else begin
                abs_row = swizz.spad_addr + ROW_IDX_WIDTH'(bank_id);
                swizz.xbar_desc.valid_mask[bank_id] = (bank_id < swizz.num_rows);
                swizz.xbar_desc.shift_mask[bank_id] = COL_IDX_WIDTH'((swizz.col_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
                swizz.xbar_desc.slot_mask[bank_id]  = abs_row;
            end
        end
    end

endmodule


