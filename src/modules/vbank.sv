module vbank #(
   parameter INDEX_WIDTH = 8,
   parameter NUM_ELEMENTS = 32,
   parameter DATA_WIDTH = 16,
   parameter NUM_ROWS = 32
)(
  input  logic clk,

  input  logic ren,
  input  logic [INDEX_WIDTH-1:0] raddr,
  output logic [DATA_WIDTH*NUM_ELEMENTS-1:0] rdata,

  input  logic wen,
  input  logic [INDEX_WIDTH-1:0] waddr,
  input  logic [DATA_WIDTH*NUM_ELEMENTS-1:0] wdata,
  input  logic [NUM_ELEMENTS-1:0] wstrb
);

  // Memory: NUM_ROWS rows, each row is a vector of NUM_ELEMENTS elements
  logic [DATA_WIDTH-1:0] mem [NUM_ROWS-1:0][NUM_ELEMENTS-1:0];

  // Read logic
  /*
  always_ff @ (posedge clk) begin
    if (ren) begin
      for (int i = 0; i < NUM_ELEMENTS; i++) begin
        rdata[i*DATA_WIDTH +: DATA_WIDTH] <= mem[raddr][i];
      end
    end
  end
  */

  // Write logic
  always_ff @ (posedge clk) begin
    if (wen) begin
      for (int i = 0; i < NUM_ELEMENTS; i++) begin
        if (wstrb[i]) begin
          mem[waddr][i] <= wdata[i*DATA_WIDTH +: DATA_WIDTH];
        end
      end
    end

    if (ren) begin
      for (int i = 0; i < NUM_ELEMENTS; i++) begin
        rdata[i*DATA_WIDTH +: DATA_WIDTH] <= mem[raddr][i];
      end
    end
  end

endmodule
