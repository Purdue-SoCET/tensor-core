`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

module frontend_sa (
    input logic clk, n_rst,
    scpad_if.frontend fif
); 
    import scpad_types_pkg::*;

    addr_map u_fe_addr_map ( 
        .row_or_col(fif.tca_frontend_req.row_or_col), 
        .base_row(fif.tca_frontend_req.base_row), 
        .row_id(fif.tca_frontend_req.row_id), .col_id(fif.tca_frontend_req.col_id), 
        .rows(fif.tca_frontend_req.num_rows), .cols(fif.tca_frontend_req.num_cols), 
        .valid_mask(fif.sa_sram_banks_req.enable_mask), .shift_mask(fif.sa_sram_banks_req.shift_mask), .slot_mask(fif.sa_sram_banks_req.slot_mask)
    );


endmodule