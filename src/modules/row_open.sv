//Implementing the open-row policy
`timescale  10ns/1ps
`include "row_open_if.vh"

module row_open (
    input logic CLK,
    input logic nRST,
    row_open_if.dut pol_if
);
    parameter int DEPTH = 16;
    typedef struct packed {
        logic [1:0] bank_group;
        logic [1:0] bank;
    } addr_t;

    typedef struct packed {
        logic valid;
        logic [15:0] row;
    } reg_t;

    reg_t [DEPTH - 1:0] reg_f, nreg_f;
    logic [1:0] nrow_stat;
    logic [8:0] nrow_conflict;
    addr_t ptr;
    assign ptr = addr_t'({pol_if.bank_group, pol_if.bank});

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
        nrow_conflict = 0;

        if (pol_if.refresh) begin
            nreg_f = 0;
        end else begin
            if (pol_if.req_en) begin
                if (reg_f[ptr].valid && reg_f[ptr].row == pol_if.row) begin
                    nrow_stat = 2'b01; //HIT
                    if (pol_if.row_resolve) begin
                        nreg_f[ptr].valid = 0;
                    end
                end else if (reg_f[ptr].valid) begin
                    nrow_stat = 2'b11; //CONFLICT
                    nrow_conflict = reg_f[ptr].row;
                    nreg_f[ptr].valid = 1'b0;
                end
                else begin
                    nreg_f[ptr].valid = 1'b1;
                    nreg_f[ptr].row = pol_if.row;
                    nrow_stat = 2'b10; //MISS
                end
            end
        end
    end

    

endmodule