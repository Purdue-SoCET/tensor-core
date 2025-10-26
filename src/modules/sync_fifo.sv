module sync_fifo #(parameter FIFODEPTH=8, DATAWIDTH=16) // DATAWIDTH = word size
(
        input logic           nRST,               // Active low reset
                            	CLK,                // Clock
                            	wr_en, 				// Write enable
                            	shift, 				// shift (increment read pointer)
        input logic  [DATAWIDTH-1:0] din, 				// Data written into FIFO
        output logic [DATAWIDTH-1:0] dout, 				// Data read from FIFO
        output logic          empty, 				// FIFO is empty when high
                            	full 				// FIFO is full when high
);


  logic [$clog2(FIFODEPTH)-1:0]   wptr;
  logic [$clog2(FIFODEPTH)-1:0]   rptr;

  logic [FIFODEPTH-1:0][DATAWIDTH-1:0] fifo; // *packed* array

  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      wptr <= '0;
      fifo <= '0;  // Initializes entire array to 0
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

  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      rptr <= '0;
      dout  <= '0;
    end else begin
      dout <= fifo[rptr]; // do not block data based on shifting (rd_en)
      if (shift & !empty) begin
        rptr <= rptr + 1;
      end
    end
  end

  assign full  = (wptr + 1) == rptr;
  assign empty = wptr == rptr;
endmodule