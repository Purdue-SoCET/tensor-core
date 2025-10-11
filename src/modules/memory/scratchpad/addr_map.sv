`include "addr_map_if.vh"

// modport backend_addr (
//         input  row_or_col,
//         input  spad_addr,
//         input  num_rows, num_cols, row_id, col_id,

//         output xbar_desc
//     );

module addr_map (
    addr_map_if.backend_addr baddr
);
    import scpad_types_pkg::*;
    logic [ROW_IDX_WIDTH-1:0] abs_row;

    for (genvar bank_id = 0; bank_id < NUM_COLS; ++bank_id) begin 
        always_comb begin
<<<<<<< Updated upstream
<<<<<<< Updated upstream
            if (rol_or_col) begin // row-major read
                slot_mask[bank_id] = base_row + row_id;
                shift_mask[bank_id]  = (bank_id < cols);
                bank_mask[bank_id]  = COL_IDX_WIDTH'((bank_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
            end else begin
                slot_mask[bank_id] = base_row + ROW_IDX_WIDTH'(bank_id);
                shift_mask[bank_id] = (bank_id < rows);
                bank_mask[bank_id]  = COL_IDX_WIDTH'((col_id ^ (abs_row & (NUM_COLS-1))) & (NUM_COLS-1));
=======
            if (baddr.row_or_col) begin // row-major read
                abs_row = baddr.spad_addr + baddr.row_id; // this is calculated everytime unnecessarily but low power cost anyways
                baddr.xbar_desc.slot_mask[bank_id] = abs_row;
                baddr.xbar_desc.valid_mask[bank_id]  = (bank_id < baddr.num_cols);
                baddr.xbar_desc.shift_mask[bank_id]  = MAX_DIM_WIDTH'(bank_id) ^ abs_row[MAX_DIM_WIDTH-1:0];
            end else begin
=======
            if (baddr.row_or_col) begin // row-major read
                abs_row = baddr.spad_addr + baddr.row_id; // this is calculated everytime unnecessarily but low power cost anyways
                baddr.xbar_desc.slot_mask[bank_id] = abs_row;
                baddr.xbar_desc.valid_mask[bank_id]  = (bank_id < baddr.num_cols);
                baddr.xbar_desc.shift_mask[bank_id]  = MAX_DIM_WIDTH'(bank_id) ^ abs_row[MAX_DIM_WIDTH-1:0];
            end else begin
>>>>>>> Stashed changes
                abs_row = baddr.spad_addr + ROW_IDX_WIDTH'(bank_id);
                baddr.xbar_desc.slot_mask[bank_id]  = abs_row;
                baddr.xbar_desc.valid_mask[bank_id] = (bank_id < baddr.num_rows);
                baddr.xbar_desc.shift_mask[bank_id] = baddr.col_id ^ abs_row[MAX_DIM_WIDTH-1:0];
<<<<<<< Updated upstream
>>>>>>> Stashed changes
=======
>>>>>>> Stashed changes
            end
        end
    end

endmodule
