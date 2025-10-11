`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module addr_map (
  input logic rol_or_col, 

  input logic [ROW_IDX_WIDTH-1:0]  base_row,

  input logic [ROW_IDX_WIDTH-1:0]  row_id,
  input logic [COL_IDX_WIDTH-1:0] col_id,

  input logic [MAX_DIM_WIDTH-1:0]  rows,     
  input logic [MAX_DIM_WIDTH-1:0]  cols,   

  output enable_mask_t valid_mask,
  output shift_mask_t shift_mask,
  output slot_mask_t slot_mask
);
    import scpad_types_pkg::*;

    always_comb begin
        bank_valid = '0;
        bank_slot = '0;
    end

    for (genvar bank_id = 0; bank_id < NUM_COLS; ++bank_id) begin 
        always_comb begin
            if (rol_or_col) begin // row-major read
                slot_mask[bank_id] = base_row + row_id;
                valid_mask[bank_id]  = (bank_id < cols);
                shift_mask[bank_id]  = COL_IDX_WIDTH'((bank_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
            end else begin
                slot_mask[bank_id] = base_row + ROW_IDX_WIDTH'(bank_id);
                valid_mask[bank_id] = (bank_id < rows);
                shift_mask[bank_id]  = COL_IDX_WIDTH'((col_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
            end
        end
    end

endmodule
