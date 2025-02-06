// register_file 
// lab 1
// rrbathin
// 8/22/2024

`include "isa_types.vh"
`include "datapath_types.vh"
`include "regfile_if.vh"

module regfile(
    input logic CLK,
    input logic nRST,
    regfile_if.rf rf_if
);

    import datapath_pkg::*;
    import isa_pkg::*;

    word_t [31:0] register, next_reg;

    always_ff @(posedge CLK, negedge nRST) begin 
        if (!nRST) begin 
            register <= '0;
        end
        else begin 
            register <= next_reg;
        end
    end
    
    always_comb begin
        next_reg = register;
        if (rf_if.WEN && (rf_if.wsel != 0)) begin 
            next_reg[rf_if.wsel] = rf_if.wdata;
        end
    end

    assign rf_if.rdat1 = register[rf_if.rsel1];
    assign rf_if.rdat2 = register[rf_if.rsel2];


endmodule