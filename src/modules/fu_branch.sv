`include "fu_branch_if.vh"
`include "datapath_types.vh"

module fu_branch(
  input logic CLK, nRST, ihit,
  fu_branch_if.btb fubif
);
  import datapath_pkg::*;

  parameter BUFFER_SIZE = 256;
  parameter IDX_SIZE    = 8;
  parameter TAG_SIZE    = 32 - IDX_SIZE - 2;
  
  logic [IDX_SIZE-1:0] pc_idx;
  logic [IDX_SIZE-1:0] pc_fetch_idx;
  logic [TAG_SIZE-1:0] pc_tag;
  logic [TAG_SIZE-1:0] pc_tag_idx;

  assign pc_idx = fubif.pc[IDX_SIZE+1:2];
  assign pc_fetch_idx = fubif.pc_fetch[IDX_SIZE+1:2];
  assign pc_tag = fubif.pc[TAG_SIZE-1+IDX_SIZE+2:IDX_SIZE+2];
  assign pc_fetch_tag = fubif.pc_fetch[31:IDX_SIZE+2];

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
      if (ihit && fubif.update_btb) begin
        buffer[pc_idx].valid <= 1'b1;
        buffer[pc_idx].tag <= pc_tag;
        buffer[pc_idx].target <= fubif.branch_target;
      end
    end
  end

  always_comb begin : OUTPUT_LOGIC
    fubif.hit = 1'b0;
    fubif.pred_target = '0;
    fubif.pred_outcome = 1'b0;

    if (buffer[pc_fetch_idx].valid && buffer[pc_fetch_idx].tag == pc_fetch_tag) begin
      fubif.hit = 1'b1;
      fubif.pred_target = buffer[pc_fetch_idx].target;

      if (buffer[pc_fetch_idx].target < fubif.pc_fetch) begin
        fubif.pred_outcome = 1'b1;
      end else begin
        fubif.pred_outcome = 1'b0;
      end
    end
  end
endmodule
