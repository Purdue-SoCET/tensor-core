module addr_mapper #(
    parameter RANK_BITS = 1,
              BANK_GROUP_BITS = 2,
              BANK_BITS = 2,
              ROW_BITS = 15,
              COLUMN_BITS = 10,
              OFFSET_BITS = 2,
              IGNORE_BITS = 1,
              CONFIG = 4            // (possible values x4, x8, x16)
) (
    input  logic [31:0] address,
    output logic [RANK_BITS - 1:0] rank,
    output logic [BANK_GROUP_BITS - 1:0] BG,
    output logic [BANK_BITS - 1:0] bank,
    output logic [ROW_BITS - 1:0] row,
    output logic [COLUMN_BITS - 1:0] col,
    output logic [OFFSET_BITS - 1:0] offset,
);

    // ignore bits for discarding extra address bits after rank bits and before row bits
    logic [IGNORE_BITS - 1:0] ignore;


    always_comb begin
        if (CONFIG == 4 || CONFIG == 8) begin
            {rank, ignore, row, bank, BG[1], col[9:3], BG[0], col[2:0], offset} = address;
        end

        // x16 has only 1 BG bit (2 BGs) 
        else if (CONFIG == 16) begin
            {rank, ignore, row, bank, BG, col, offset} = address;
        end
    end
    
endmodule

