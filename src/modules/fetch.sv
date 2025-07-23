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

        if ((fif.misprediction || fif.br_jump) && !fif.freeze) begin
            next_pc = fif.correct_pc;
        end
        
        if (fif.freeze) begin
            next_pc = pc_reg;
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin : REG_LOGIC
        if (!nRST) begin
            pc_reg <= PC_INIT;
            fif.instr <= '0;
            imemaddr <= '0;
            fif.pc <= '0;
        end else begin
            if (fif.br_jump) begin
                fif.pc <= next_pc;
                pc_reg <= next_pc;
                imemaddr <= next_pc;
            end
            else if (fif.jump && !fif.missed) begin
                pc_reg <= '0;
                fif.instr <= '0;
                fif.pc <= '0;
            end
            else begin
                if (ihit) begin
                    imemaddr <= next_pc;
                end

                if ((ihit && !fif.freeze) || (fif.missed && ihit)) begin
                    pc_reg <= next_pc;
                    fif.instr <= fif.imemload;
                    fif.pc <= imemaddr;
                    // imemaddr <= next_pc;
                end
                else if (fif.freeze) begin
                    pc_reg <= pc_reg;
                    fif.instr <= fif.instr;
                    fif.pc <= fif.pc;
                end
                else begin
                    pc_reg <= '0;
                    fif.instr <= '0;
                    fif.pc <= '0;
                end
            end
        end
    end

    assign fif.imemaddr = imemaddr;
    // assign fif.pc = pc_reg;
    assign fif.imemREN = !fif.freeze && !fif.br_jump;
endmodule