`include "cache_types_pkg.svh";

module vector_bank # (
    parameter INDEX_WIDTH = 8,
    parameter NUM_WORD_PER_BLOCK = 4
)(
  input logic clk,

  input logic ren,
  input logic [INDEX_WIDTH-1:0] raddr,
  output logic [31:0] rdata,

  input logic wen,
  input logic [INDEX_WIDTH-1:0] waddr,
  input logic [31:0] wdata,
  input logic [NUM_WORD_PER_BLOCK-1:0] wstrb
);
  cache_block [NUM_SETS_PER_WAY-1:0] mem;

  always_ff @ (posedge clk) begin
    if (ren) begin
      rdata <= mem[raddr];
    end
  end

  always_ff @ (posedge clk) begin
    if (wen) begin
      for (int b = 0; b < NUM_BYTE_PER_BLOCK; b++) begin
        if (wstrb[b]) begin
          mem[waddr][31*b +: 31] <= wdata[31*b +: 31];
        end
      end
    end
  end
endmodule