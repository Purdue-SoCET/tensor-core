module _sram_bank #(
  parameter int ELEM_BITS = 16,
  parameter int NUM_ROWS = 128,
  parameter int ROW_IDX_WIDTH  = $clog2(NUM_ROWS)
)(
  input logic clk,

  input logic ren,
  input logic [ROW_IDX_WIDTH-1:0]  raddr,
  output logic [ELEM_BITS-1:0] rdata,

  input logic wen,
  input logic [ROW_IDX_WIDTH-1:0] waddr,
  input logic [ELEM_BITS-1:0] wdata
);

  logic [ELEM_BITS-1:0] mem [0:NUM_ROWS-1];

  always_ff @ (posedge clk) begin
    if (ren) begin
      rdata <= mem[raddr];
    end
  end

  always_ff @ (posedge clk) begin
    if (wen) begin
      mem[waddr] <= wdata;
    end
  end

endmodule
