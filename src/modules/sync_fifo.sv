module sync_fifo #(parameter FIFODEPTH=8, DATAWIDTH=16) // DATAWIDTH = word size
(
        input logic           rstn,               // Active low reset
                            	clk,                // Clock
                            	wr_en, 				// Write enable
                            	rd_en, 				// Read enable
        input logic  [DATAWIDTH-1:0] din, 				// Data written into FIFO
        output logic [DATAWIDTH-1:0] dout, 				// Data read from FIFO
        output logic          empty, 				// FIFO is empty when high
                            	full 				// FIFO is full when high
);


  logic [$clog2(FIFODEPTH)-1:0]   wptr;
  logic [$clog2(FIFODEPTH)-1:0]   rptr;
  logic [$clog2(FIFODEPTH):0]     count; // one extra bit to represent full==depth

  logic [FIFODEPTH-1:0][DATAWIDTH-1:0] fifo; // *packed* array

  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
      wptr <= '0;
    end 
    else begin
      if (wr_en & !full) begin
        fifo[wptr] <= din;
        wptr <= wptr + 1;
      end
    end
  end

  // For debug
  /*
  initial begin
    $monitor("[%0t] [FIFO] wr_en=%0b din=0x%0h rd_en=%0b dout=0x%0h empty=%0b full=%0b",
             $time, wr_en, din, rd_en, dout, empty, full);
  end */

  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
      rptr <= '0;
      dout  <= '0;
    end else begin
      dout <= fifo[rptr]; // do not block data based on rd_en
      if (rd_en & !empty) begin
        rptr <= rptr + 1;
      end
    end
  end

  // count logic (synchronous)
  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
      count <= '0;
    end else begin
      case ({wr_en & ~full, rd_en & ~empty})
        2'b10: count <= count + 1; // write only
        2'b01: count <= count - 1; // read only
        default: count <= count;   // both or neither
      endcase
    end
  end

  assign full  = (count == FIFODEPTH);
  assign empty = (count == 0);

  // assign full  = (wptr + 1) == rptr;
  // assign empty = wptr == rptr;
endmodule