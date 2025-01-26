// `include "fu_branchpred_if.vh"
// `include "cpu_types.vh"
// `include "types_pkg.vh"

module fu_branchpred(
  input logic CLK, nRST, ihit,
  fu_branchpred_if.btb fubpif
);
  import cpu_types::*;
  import types_pkg::*;

  parameter BUFFER_SIZE = 256;
  parameter IDX_SIZE    = 8;
  parameter TAG_SIZE    = 32 - IDX_SIZE - 2;

  logic [IDX_SIZE-1:0] pc_idx;
  logic [IDX_SIZE-1:0] pc_fetch_idx;
  logic [TAG_SIZE-1:0] pc_tag;
  logic [TAG_SIZE-1:0] pc_fetch_tag;

  assign pc_idx = fubpif.pc[IDX_SIZE+1:2];
  assign pc_fetch_idx = fubpif.pc_fetch[IDX_SIZE+1:2];
  assign pc_tag = fubpif.pc[31:IDX_SIZE+2];
  assign pc_fetch_tag = fubpif.pc_fetch[31:IDX_SIZE+2];

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
      // update_btb should be high when branch signal from control unit is high
      if (ihit && fubpif.update_btb) begin
        buffer[pc_idx].valid <= 1'b1;
        buffer[pc_idx].tag <= pc_tag;
        buffer[pc_idx].target <= fubpif.branch_target;
      end
    end
  end

  always_comb begin : OUTPUT_LOGIC
    fubpif.pred_target = '0;
    fubpif.pred_outcome = 1'b0;
    fubpif.hit = 1'b0;

    if (buffer[pc_fetch_idx].valid && buffer[pc_fetch_idx].tag == pc_fetch_tag) begin
      fubpif.hit = 1'b1;
      fubpif.pred_target = buffer[pc_fetch_idx].target;

      if (buffer[pc_fetch_idx].target < fubpif.pc_fetch) begin
        fubpif.pred_outcome = 1'b1;
      end else begin
        fubpif.pred_outcome = 1'b0;
      end
    end
  end
endmodule