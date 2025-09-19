`include "scpad_types_pkg.vh"
`include "scratchpad_if.vh"

// This unit interfaces with the Queue Pair from the Backend 
// Assume that the values coming in from the input port are always held level-high. 
// You do not need a skid-buffer to deal with situations were there are slot conflicts. 
// The WAR hazard problem will be dealt with in the scheduler based on the addresses passed in from the instructions. 
// Our only worry here is when do we issue a read/write into the SRAM banks. Priority given to the reads during conflicts. 

module sram_cntrl (
    input logic clk, n_rst,
    scpad_if.sram srif, 
    logic [NUM_COLS-1:0] ren, wen, rdone, wdone,
    logic [ROW_IDX_WIDTH-1:0] raddr, waddr
); 
    import scpad_types_pkg::*;

    logic conflict;
    logic [NUM_COLS-1:0] bank_conflicts; 

    always_comb begin
        bank_conflicts = '0;
        for (int i = 0; i < NUM_COLS; i++) begin
            bank_conflicts[i] = (srif.backend_sram_banks_req.valid & srif.frontend_sram_banks_req.valid) & 
            (srif.backend_sram_banks_req.enable_mask[i] & srif.frontend_sram_banks_req.enable_mask[i]) & 
            (srif.backend_sram_banks_req.slot_mask[i] == srif.frontend_sram_banks_req.slot_mask[i]);
        end
    end

    assign conflict = |bank_conflicts; 

    assign ren = (srif.frontend_sram_banks_req.valid) ? srif.frontend_sram_banks_req.enable_mask : '0; 
    assign raddr = srif.frontend_sram_banks_req.slot_mask;
    
    assign waddr = srif.backend_sram_banks_req.slot_mask;
    assign wen = (srif.backend_sram_banks_req.valid & !conflict) ? srif.backend_sram_banks_req.enable_mask : '0; 

    assign srif.frontend_sram_banks_res.valid = (srif.frontend_sram_banks_req.valid) ? (&(rdone | ~srif.frontend_sram_banks_req.enable_mask)) : 1'b0; 
    assign srif.backend_sram_banks_res.valid = (srif.backend_sram_banks_req.valid && !conflict)  ? (&(wdone | ~srif.backend_sram_banks_req.enable_mask)) : 1'b0; 

endmodule