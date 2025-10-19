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
            if (baddr.row_or_col) begin // row-major read
                abs_row = baddr.spad_addr[9:5] + baddr.row_id; // this is calculated everytime unnecessarily but low power cost anyways
                baddr.xbar_desc.slot_mask[bank_id] = abs_row;
                baddr.xbar_desc.valid_mask[bank_id]  = (bank_id < baddr.num_cols);
                baddr.xbar_desc.shift_mask[bank_id]  = MAX_DIM_WIDTH'(bank_id) ^ abs_row[MAX_DIM_WIDTH-1:0];
            end else begin
                abs_row = baddr.spad_addr[9:5] + ROW_IDX_WIDTH'(bank_id);
                baddr.xbar_desc.slot_mask[bank_id]  = abs_row;
                baddr.xbar_desc.valid_mask[bank_id] = (bank_id < baddr.num_rows);
                baddr.xbar_desc.shift_mask[bank_id] = baddr.col_id ^ abs_row[MAX_DIM_WIDTH-1:0];
            end
        end
    end

endmodule
