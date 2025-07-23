// `include "fu_branch_if.vh"
// `include "isa_types.vh"

// module fu_branch(
//   input logic CLK, nRST,
//   fu_branch_if.br fubif
// );
//   import isa_pkg::*;

//   logic zero;
//   logic actual_outcome;
//   logic resolved, delay;

//   // Track if BTB has been updated for current branch instr
//   logic btb_updated;
//   logic [31:0] last_branch_pc;

//   word_t updated_pc;

//   always_ff @(posedge CLK, negedge nRST) begin
//     if (!nRST) begin
//       btb_updated <= 1'b0;
//       last_branch_pc <= 32'h0;
//     end else begin
//       if (fubif.enable && fubif.j_type == 2'd0) begin
//         if (fubif.current_pc != last_branch_pc) begin
//           // New branch instruction arrived so reset btb_updated
//           btb_updated <= 1'b0;
//         end

//         if (!btb_updated) begin
//           btb_updated <= 1'b1;
//         end

//         // Update last branch PC
//         last_branch_pc <= fubif.current_pc;
//       end else begin
//         // Not a branch
//         btb_updated   <= 1'b0;
//         last_branch_pc <= 32'h0;
//       end
//     end
//   end

//   always_comb begin : ZERO_LOGIC
//     zero = '0;

//     casez (fubif.branch_type)
//       BT_BEQ: zero = fubif.reg_a - fubif.reg_b == 0;
//       BT_BNE: zero = fubif.reg_a - fubif.reg_b == 0;
//       BT_BLT: zero = ($signed(fubif.reg_a) < $signed(fubif.reg_b));
//       BT_BGE: zero = ($signed(fubif.reg_a) < $signed(fubif.reg_b));
//       BT_BLTU: zero = (fubif.reg_a < fubif.reg_b);  
//       BT_BGEU: zero = (fubif.reg_a < fubif.reg_b);
//       default:  zero = 1'b0;   
//     endcase
//   end

//   // always_ff @(posedge CLK, negedge nRST) begin
//   //   if (!nRST) begin
//   //     resolved <= 0;
//   //   end
//   //   else begin
//   //     resolved <= delay;
//   //   end
//   // end

//   // All logic assumes the immediate is that is passed in is already decoded
//   always_comb begin : BRANCH_LOGIC
//     // updated_pc is corrected PC after branch resolution (ignore during correct prediction)
//     // update_pc is original PC of branch instr being resolved (used to update the BTB)
//     fubif.branch_outcome = 1'b0;
//     fubif.miss = 1'b0;
//     updated_pc = fubif.current_pc + 32'd4;
//     fubif.correct_pc = fubif.current_pc + 32'd4;
//     fubif.branch_target = '0;
//     fubif.update_btb = 1'b0;
//     fubif.update_pc = '0;
//     fubif.resolved = 1'b0;
//     actual_outcome = '0;
//     fubif.jump_dest = '0;
//     fubif.jump_wdat = '0;
//     fubif.br_jump = '0;
//     // delay = 1'b0;

//     if (fubif.enable) begin
//       if (fubif.j_type != 2'd0) begin
//         actual_outcome = 1'b1;
//         fubif.br_jump = 1'b1;

//         casez (fubif.j_type)
//           // JAL
//           2'd1: begin
//             updated_pc = fubif.current_pc + fubif.imm;
//             fubif.jump_wdat = fubif.current_pc + 32'd4;
//             fubif.resolved = 1'b1;
//             // delay = 1'b1;
//           end
//           // JALR
//           2'd2: begin
//             updated_pc = fubif.reg_a + fubif.imm;
//             fubif.jump_wdat = fubif.current_pc + 32'd4;
//             fubif.resolved = 1'b1;
//             // delay = 1'b1;
//           end
//           default: begin
//             updated_pc = fubif.current_pc + 32'd4;
//           end
//         endcase

//         fubif.correct_pc = updated_pc;
//         // fubif.resolved = 1'b1;
//       end else begin
//         casez (fubif.branch_type)
//           BT_BEQ: actual_outcome = zero;
//           BT_BNE: actual_outcome = ~zero;
//           BT_BLT: actual_outcome = zero;
//           BT_BGE: actual_outcome = ~zero;
//           BT_BLTU: actual_outcome = zero;
//           BT_BGEU: actual_outcome = ~zero;
//           default: actual_outcome = 1'b0;
//         endcase

//         updated_pc = actual_outcome ? (fubif.current_pc + fubif.imm) : (fubif.current_pc + 32'd4);
//         fubif.branch_target = fubif.current_pc + fubif.imm;
//         fubif.correct_pc = updated_pc;
//         fubif.branch_outcome = actual_outcome;
//         fubif.miss = (actual_outcome != fubif.predicted_outcome);

//         // enable will control when the BTB can update
//         // btb_updated will only allow one update per branch instruction
//         if (!btb_updated) fubif.update_btb = 1'b1;
//         fubif.resolved = !fubif.miss;
        
//         fubif.update_pc = fubif.current_pc;
//       end
//     end 
//   end
// endmodule

// Modified version below

`include "fu_branch_if.vh"
`include "isa_types.vh"

module fu_branch(
  input logic CLK, nRST,
  fu_branch_if.br fubif
);
  import isa_pkg::*;

  logic zero;
  logic actual_outcome;
  logic resolved, delay;

  // Temporary variables for one-cycle delay (attempt to break critical path)
  logic temp_branch_outcome;
  logic temp_miss;
  word_t temp_correct_pc;
  word_t temp_branch_target;
  logic temp_update_btb;
  word_t temp_update_pc;
  logic temp_resolved;
  word_t temp_jump_dest;
  word_t temp_jump_wdat;
  logic temp_br_jump;

  // Track if BTB has been updated for current branch instr
  logic btb_updated;
  logic [31:0] last_branch_pc;

  word_t updated_pc;

  always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
      btb_updated <= 1'b0;
      last_branch_pc <= 32'h0;
    end else begin
      if (fubif.enable && fubif.j_type == 2'd0) begin
        if (fubif.current_pc != last_branch_pc) begin
          // New branch instruction arrived so reset btb_updated
          btb_updated <= 1'b0;
        end

        if (!btb_updated) begin
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

    casez (fubif.branch_type)
      BT_BEQ: zero = fubif.reg_a - fubif.reg_b == 0;
      BT_BNE: zero = fubif.reg_a - fubif.reg_b == 0;
      BT_BLT: zero = ($signed(fubif.reg_a) < $signed(fubif.reg_b));
      BT_BGE: zero = ($signed(fubif.reg_a) < $signed(fubif.reg_b));
      BT_BLTU: zero = (fubif.reg_a < fubif.reg_b);  
      BT_BGEU: zero = (fubif.reg_a < fubif.reg_b);
      default:  zero = 1'b0;   
    endcase
  end

  // always_ff @(posedge CLK, negedge nRST) begin
  //   if (!nRST) begin
  //     resolved <= 0;
  //   end
  //   else begin
  //     resolved <= delay;
  //   end
  // end



  // All logic assumes the immediate is that is passed in is already decoded
  always_comb begin : BRANCH_LOGIC
    // updated_pc is corrected PC after branch resolution (ignore during correct prediction)
    // update_pc is original PC of branch instr being resolved (used to update the BTB)
    temp_branch_outcome = 1'b0;
    temp_miss = 1'b0;

    updated_pc = fubif.current_pc + 32'd4;

    temp_correct_pc = fubif.current_pc + 32'd4;
    temp_branch_target = '0;
    temp_update_btb = 1'b0;
    temp_update_pc = '0;
    temp_resolved = 1'b0;

    actual_outcome = '0;

    temp_jump_dest = '0;
    temp_jump_wdat = '0;
    temp_br_jump = '0;
    // delay = 1'b0;

    if (fubif.enable) begin
      if (fubif.j_type != 2'd0) begin
        actual_outcome = 1'b1;
        temp_br_jump = 1'b1;

        casez (fubif.j_type)
          // JAL
          2'd1: begin
            updated_pc = fubif.current_pc + fubif.imm;
            temp_jump_wdat = fubif.current_pc + 32'd4;
            temp_resolved = 1'b1;
            // delay = 1'b1;
          end
          // JALR
          2'd2: begin
            updated_pc = fubif.reg_a + fubif.imm;
            temp_jump_wdat = fubif.current_pc + 32'd4;
            temp_resolved = 1'b1;
            // delay = 1'b1;
          end
          default: begin
            updated_pc = fubif.current_pc + 32'd4;
          end
        endcase

        temp_correct_pc = updated_pc;
        // fubif.resolved = 1'b1;
      end else begin
        casez (fubif.branch_type)
          BT_BEQ: actual_outcome = zero;
          BT_BNE: actual_outcome = ~zero;
          BT_BLT: actual_outcome = zero;
          BT_BGE: actual_outcome = ~zero;
          BT_BLTU: actual_outcome = zero;
          BT_BGEU: actual_outcome = ~zero;
          default: actual_outcome = 1'b0;
        endcase

        updated_pc = actual_outcome ? (fubif.current_pc + fubif.imm) : (fubif.current_pc + 32'd4);
        temp_branch_target = fubif.current_pc + fubif.imm;
        temp_correct_pc = updated_pc;
        temp_branch_outcome = actual_outcome;
        temp_miss = (actual_outcome != fubif.predicted_outcome);

        // enable will control when the BTB can update
        // btb_updated will only allow one update per branch instruction
        if (!btb_updated) temp_update_btb = 1'b1;
        temp_resolved = !temp_miss;
        
        temp_update_pc = fubif.current_pc;
      end
    end 
  end
 


always_ff @(posedge CLK, negedge nRST) begin : BRANCH_LOGIC_clocked
    // updated_pc is corrected PC after branch resolution (ignore during correct prediction)
    // update_pc is original PC of branch instr being resolved (used to update the BTB)
    if (!nRST || fubif.miss || fubif.resolved) begin
    fubif.branch_outcome <= 1'b0;
    fubif.miss <= 1'b0;

    fubif.correct_pc <= fubif.current_pc + 32'd4;
    fubif.branch_target <= '0;
    fubif.update_btb <= 1'b0;
    fubif.update_pc <= '0;
    fubif.resolved <= 1'b0;
   
    fubif.jump_dest <= '0;
    fubif.jump_wdat <= '0;
    fubif.br_jump <= '0;
    // delay = 1'b0;
    end
    else begin

    fubif.branch_outcome <= temp_branch_outcome;
    fubif.miss <= temp_miss;
    
    fubif.correct_pc <= temp_correct_pc;
    fubif.branch_target <= temp_branch_target;
    fubif.update_btb <= temp_update_btb;
    fubif.update_pc <= temp_update_pc;
    fubif.resolved <= temp_resolved;
    
    fubif.jump_dest <= temp_jump_dest;
    fubif.jump_wdat <= temp_jump_wdat;
    fubif.br_jump <= temp_br_jump;
      
    end 
  end
endmodule