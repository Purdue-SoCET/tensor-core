//Implementing the open-row policy
`timescale 1ps/1ps
`include "row_open_if.vh"
`include "dram_pkg.vh"

module row_open # (
    parameter DEPTH = 16
) (
    input logic CLK,
    input logic nRST,
    row_open_if.row_open pol_if,
    address_mapper_if.row_open amif
);
    import dram_pkg::*;
    // parameter int DEPTH = 16;
    typedef struct packed {
        logic [BANK_GROUP_BITS - 1:0] bank_group;
        logic [BANK_BITS - 1:0] bank;
    } addr_t;

    typedef struct packed {
        logic valid;
        logic [ROW_BITS - 1:0] row;
    } reg_t;

    reg_t [DEPTH - 1:0] reg_f, nreg_f;
    logic [1:0] nrow_stat;
    logic [ROW_BITS - 1:0] nrow_conflict;
    addr_t ptr;
    assign ptr = addr_t'({amif.BG, amif.bank});

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            reg_f <= 0;
            pol_if.row_stat <= 0;
            pol_if.row_conflict <= 0;
            
        end else begin
            reg_f <= nreg_f;
            pol_if.row_stat <= nrow_stat;
            pol_if.row_conflict <= nrow_conflict;
        end
    end

    always_comb begin
        nreg_f = reg_f;
        nrow_stat = 0;
        nrow_conflict = pol_if.row_conflict;

        if (pol_if.refresh) begin
            nreg_f = 0;
        end else begin
            if (pol_if.req_en) begin
                if (reg_f[ptr].valid && reg_f[ptr].row == amif.row) begin
                    nrow_stat = 2'b01; //HIT
                    if (pol_if.row_resolve) begin
                        nreg_f[ptr].valid = 0;
                    end
                end else if (reg_f[ptr].valid) begin
                    nrow_stat = 2'b11; //CONFLICT
                    nrow_conflict = reg_f[ptr].row;
                    if (pol_if.row_resolve) begin
                        nreg_f[ptr].valid = 0;
                        nrow_stat = 2'b0; //IDLE
                    end
                    
                end
                else begin
                    nreg_f[ptr].valid = 1'b1;
                    nreg_f[ptr].row = amif.row;
                    nrow_stat = 2'b10; //MISS
                end
            end
        end
    end
endmodule