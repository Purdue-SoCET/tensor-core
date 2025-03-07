`include "fu_branch_if.vh"
`include "isa_types.vh"

module fu_branch(
  input logic CLK, nRST,
  fu_branch_if.br fubif
);
  import isa_pkg::*;

  logic zero;
  logic actual_outcome;

  // Track if BTB has been updated for current branch instr
  logic btb_updated;
  logic [31:0] last_branch_pc;

  always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
      btb_updated <= 1'b0;
      last_branch_pc <= 32'h0;
    end else begin
      if (fubif.branch) begin
        if (fubif.current_pc != last_branch_pc) begin
          // New branch instruction arrived so reset btb_updated
          btb_updated <= 1'b0;
        end

        if (fubif.enable && !btb_updated) begin
          btb_updated <= 1'b1;
        end

        // Update last branch PC
        last_branch_pc <= fubif.current_pc;
      end else begin
        // Not a branch
        btb_updated   <= 1'b0;
        last_branch_pc <= 32'h0;
      end
    end
  end

  always_comb begin : ZERO_LOGIC
    zero = '0;

    case (fubif.branch_type)
      2'd0: zero = fubif.reg_a - fubif.reg_b == 0;                               // 2'd0: BEQ, BNE
      2'd1: zero = ($signed(fubif.reg_a) < $signed(fubif.reg_b)) ? 1'b0 : 1'b1;  // 2'd1: BLT, BGE
      2'd2: zero = (fubif.reg_a < fubif.reg_b) ? 1'b0 : 1'b1;                    // 2'd2: BLTU, BGEU
      default: zero = 1'b0;   
    endcase
  end

  always_comb begin : BRANCH_LOGIC
    // updated_pc is corrected PC after branch resolution (ignore during correct prediction)
    // update_pc is original PC of branch instr being resolved (used to update the BTB)
    fubif.branch_outcome = 1'b0;
    fubif.misprediction = 1'b0;
    fubif.updated_pc = fubif.current_pc + 32'd4;
    fubif.correct_pc = fubif.current_pc + 32'd4;
    fubif.branch_target = '0;
    fubif.update_btb = 1'b0;
    fubif.update_pc = '0;
    actual_outcome = '0;

    if (fubif.branch) begin
      actual_outcome = fubif.branch_gate_sel ? ~zero : zero;
      fubif.branch_outcome = actual_outcome;
      fubif.updated_pc = actual_outcome ? (fubif.current_pc + fubif.imm) : (fubif.current_pc + 32'd4);

      fubif.misprediction = (actual_outcome != fubif.predicted_outcome);
      fubif.correct_pc = fubif.updated_pc;

      // enable will control when the BTB can update
      // btb_updated will only allow one update per branch instruction
      if (fubif.enable && !btb_updated) fubif.update_btb = 1'b1;
      
      fubif.update_pc = fubif.current_pc;
      fubif.branch_target = fubif.current_pc + fubif.imm;
    end 
  end
endmodule