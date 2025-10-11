`include "dram_pkg.vh"
`include "address_mapper_if.vh"

module addr_mapper #(
    // parameter RANK_BITS = 1,
    //           BANK_GROUP_BITS = 2,
    //           BANK_BITS = 2,
    //           ROW_BITS = 15,
    //           COLUMN_BITS = 10,
    //           OFFSET_BITS = 2,
    //           IGNORE_BITS = 1,
    //           CONFIGS = 4            // (possible values x4, x8, x16)
) (
    // input  logic [31:0] address,
    // output logic [RANK_BITS - 1:0] rank,
    // output logic [BANK_GROUP_BITS - 1:0] BG,
    // output logic [BANK_BITS - 1:0] bank,
    // output logic [ROW_BITS - 1:0] row,
    // output logic [COLUMN_BITS - 1:0] col,
    // output logic [OFFSET_BITS - 1:0] offset,

    address_mapper_if.addr_mapper amif
);
    import dram_pkg::*;
    // ignore bits for discarding extra address bits after rank bits and before row bits
    // logic [IGNORE_BITS - 1:0] ignore;


    always_comb begin 
        {amif.rank, amif.row, amif.bank, amif.BG[1], amif.col[9:3], amif.BG[0], amif.col[2:0], amif.offset} = 0;
        if (amif.configs == x4 || amif.configs == x8) begin
            //TODO: The address mapper is ok we we need to make somechange 
            // {amif.rank, amif.row, amif.bank, amif.BG[1], amif.col[9:3], amif.BG[0], amif.col[2:0], amif.offset} = amif.address;
            //The offset of the burst can use to mux to give back to data transfer, but writing, we want to ensure that it start with 0 first
            {amif.rank, amif.row, amif.bank, amif.BG[1], amif.col[9:3], amif.BG[0], amif.col[2:0], amif.offset} = {amif.address[30:6],3'b0,amif.address[1:0]};
        end
        // x16 has only 1 BG bit (2 BGs) 
        else if (amif.configs == x16) begin
            {amif.rank, amif.row, amif.bank, amif.BG, amif.col, amif.offset} = amif.address;
        end
    end
    
endmodule
