`include "fetch_if.vh"
`include "isa_types.vh"

module fetch(
    input logic CLK, nRST, ihit,
    fetch_if.ft fif
);
    import isa_pkg::*;

    parameter PC_INIT = 32'd0;
    word_t pc_reg, next_pc;

    always_comb begin
        next_pc = fif.pc_prediction;

        if (fif.misprediction) begin
            next_pc = fif.correct_pc;
        end else if (fif.stall || !fif.dispatch_free) begin
            next_pc = pc_reg;
        end else begin
            next_pc = fif.pc_prediction;
        end
    end

    always_ff @(posedge CLK, negedge nRST) begin : REG_LOGIC
        if (!nRST) begin
            pc_reg <= PC_INIT;
        end else begin
            if (ihit && !fif.stall && fif.dispatch_free) begin
                pc_reg <= next_pc;
            end
        end
    end

    assign fif.pc = pc_reg;
    assign fif.instr = fif.imemload;
endmodule