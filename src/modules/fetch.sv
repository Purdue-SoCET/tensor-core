`include "fetch_if.vh"
`include "isa_types.vh"

module fetch(
    input logic CLK, nRST, ihit,
    fetch_if.ft fif
);
    import isa_pkg::*;

    parameter PC_INIT = 32'd0;
    word_t pc_reg, next_pc, imemaddr;

    always_comb begin 
        next_pc = fif.pc_prediction;
        if (fif.freeze) begin
            next_pc = pc_reg;
        end else if (fif.misprediction || fif.br_jump) begin
            next_pc = fif.correct_pc;
        end
    end 

    always_ff @(posedge CLK, negedge nRST) begin : REG_LOGIC
        if (!nRST) begin
            pc_reg    <= PC_INIT;
            imemaddr  <= '0;
            fif.instr <= '0;
            fif.pc    <= '0;
        end else if (fif.br_jump) begin
            pc_reg    <= next_pc;
            fif.pc    <= next_pc;
            imemaddr  <= next_pc;
        end else if (fif.jump && !fif.missed) begin
            pc_reg    <= '0;
            fif.instr <= '0;
            fif.pc    <= '0;
        end else if (fif.freeze) begin
            pc_reg  <= pc_reg;
            fif.pc  <= fif.pc;
        end else if ((ihit && !fif.freeze) || (fif.missed && ihit)) begin // this is just a valid memory access so we fetch inst and update pc
            pc_reg    <= next_pc;
            fif.instr <= fif.imemload;
            fif.pc    <= imemaddr;
            imemaddr  <= next_pc;
        end else if (ihit) begin
            imemaddr <= next_pc;
        end else begin
            pc_reg    <= '0;
            fif.instr <= '0;
            fif.pc    <= '0;
        end
    end
/*Instruction Fetch Interface (to icache):
    - fif.imemaddr -> sent to dcif.imemaddr
    - fif.imemREN -> sent to dcif.imemREN
    - fif.imemload <-  receives instruction from dcif.imemload
    - fif.ihit <- indicates hit status from dcif.ihit
*/
    assign fif.imemaddr = imemaddr;
    assign fif.imemREN = !fif.freeze;
endmodule