// `include "fu_branch_if.vh"
// `include "cpu_types.vh"
// `include "types_pkg.vh"

module fu_branch(
  input logic CLK, nRST,
  fu_branch_if.br fubif
);
  import cpu_types::*;
  import types_pkg::*;

  logic zero;

  always_comb begin : ZERO_LOGIC
    zero = '0;

    casez (fubif.branch_type)
      2'd0: zero = (fubif.reg_a - fubif.reg_b) ? 1'b0 : 1'b1;                    // 2'd0: BEQ, BNE
      2'd1: zero = ($signed(fubif.reg_a) < $signed(fubif.reg_b)) ? 1'b0 : 1'b1;  // 2'd1: BLT, BGE
      2'd2: zero = (fubif.reg_a < fubif.reg_b) ? 1'b0 : 1'b1;                    // 2'd2: BLTU, BGEU
    endcase
  end

  always_comb begin : BRANCH_LOGIC
    fubif.branch_outcome = '0;
    fubif.updated_pc = fubif.current_pc + 32'd4;

    if (fubif.branch) begin
      casez (fubif.branch_gate_sel)
        1'b0: fubif.branch_outcome = zero;    // 1'b0: BEQ, BGE, BGEU
        1'b1: fubif.branch_outcome = ~zero;   // 1'b1: BNE, BLT, BLTU
      endcase

      if (fubif.branch_outcome) fubif.updated_pc = fubif.current_pc + fubif.imm;
    end
  end
endmodule