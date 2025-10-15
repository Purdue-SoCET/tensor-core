import scpad_pkg::*;

module swizzle (
  input logic rol_or_col, 

  input logic [ROW_IDX_WIDTH-1:0] base_row,
  input logic [ROW_IDX_WIDTH-1:0] row_id,
  input logic [COL_IDX_WIDTH-1:0] col_id,
  input logic [MAX_DIM_WIDTH-1:0] rows,     
  input logic [MAX_DIM_WIDTH-1:0] cols,   

  output mask_t valid_mask,
  output shift_mask_t shift_mask,
  output slot_mask_t slot_mask
);

    logic [ROW_IDX_WIDTH-1:0] abs_row;

    always_comb begin
        valid_mask = '0;
        shift_mask = '0;
        slot_mask  = '0;

        for (int bank_id = 0; bank_id < NUM_COLS; bank_id++) begin
            if (rol_or_col) begin // row-major read
                abs_row = base_row + row_id;
                valid_mask[bank_id] = (bank_id < cols);
                shift_mask[bank_id] = COL_IDX_WIDTH'((bank_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
                slot_mask[bank_id]  = abs_row;
            end else begin
                abs_row = base_row + ROW_IDX_WIDTH'(bank_id);
                valid_mask[bank_id] = (bank_id < rows);
                shift_mask[bank_id] = COL_IDX_WIDTH'((col_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
                slot_mask[bank_id]  = abs_row;
            end
        end
    end

endmodule


