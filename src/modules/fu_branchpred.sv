// `include "fu_branchpred_if.vh"
// `include "cpu_types.vh"
// `include "types_pkg.vh"

module fu_branchpred(
  input logic CLK, nRST,
  fu_branchpred_if.btb fubpif
);
  import cpu_types::*;
  import types_pkg::*;

  parameter WORD_W      = 32;
  parameter BUFFER_SIZE = 256;
  parameter IDX_SIZE    = 8;
  parameter TAG_SIZE    = WORD_W - IDX_SIZE - 2;

  logic [IDX_SIZE-1:0] pc_idx;
  logic [IDX_SIZE-1:0] update_pc_idx;
  logic [TAG_SIZE-1:0] pc_tag;
  logic [TAG_SIZE-1:0] update_pc_tag;

  logic btb_hit;
  word_t btb_target;

  // Extract indices from pc and update_pc (lower 2 bits are ignored due to word alignment)
  assign pc_idx = fubpif.pc[IDX_SIZE+1:2];
  assign update_pc_idx = fubpif.update_pc[IDX_SIZE+1:2];

  // Extract tag from pc and update_pc
  assign pc_tag = fubpif.pc[WORD_W-1:IDX_SIZE+2];
  assign update_pc_tag = fubpif.update_pc[WORD_W-1:IDX_SIZE+2];

  // Buffer Type
  typedef struct packed {
    word_t target;
    logic [TAG_SIZE-1:0] tag;
    logic valid;
  } btb_t;

  btb_t [BUFFER_SIZE-1:0] buffer;

  always_ff @(posedge CLK, negedge nRST) begin : REG_LOGIC
    if (nRST == 1'b0) begin
      buffer <= '0;
    end else begin
      // update_btb should be high when branch instruction is processed
      if (fubpif.update_btb) begin
        // Update BTB for taken branches only
        // TODO: Test this optimization
        if (fubpif.branch_outcome) begin
          buffer[update_pc_idx].valid <= 1'b1;
          buffer[update_pc_idx].tag <= update_pc_tag;
          buffer[update_pc_idx].target <= fubpif.branch_target;
        end else begin
          // Invalidate entries for branches that are not taken
          buffer[update_pc_idx].valid <= 1'b0;
        end
      end
    end
  end

  assign btb_hit = buffer[pc_idx].valid && (buffer[pc_idx].tag == fubpif.pc[WORD_W-1:IDX_SIZE+2]);
  assign btb_target = buffer[pc_idx].target;

  always_comb begin : OUTPUT_LOGIC
    fubpif.predicted_outcome = 1'b0;
    fubpif.predicted_target = fubpif.pc + 4;

    if (btb_hit) begin
      fubpif.predicted_outcome = (btb_target < fubpif.pc);
    end

    if (fubpif.predicted_outcome) begin
      fubpif.predicted_target = btb_target;
    end
  end
endmodule