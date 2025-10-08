module sync_fifo #(parameter FIFODEPTH=8, DATAWIDTH=16) // DATAWIDTH = word size
(
        input               	rstn,               // Active low reset
                            	clk,                // Clock
                            	wr_en, 				// Write enable
                            	rd_en, 				// Read enable
        input      [DDATAWIDTH-1:0] din, 				// Data written into FIFO
        output logic [DDATAWIDTH-1:0] dout, 				// Data read from FIFO
        output              	empty, 				// FIFO is empty when high
                            	full 				// FIFO is full when high
);


  logic [$clog2(FIFODEPTH)-1:0]   wptr;
  logic [$clog2(FIFODEPTH)-1:0]   rptr;

  logic [DDATAWIDTH-1 : 0][FIFODEPTH] fifo; // *packed* array

  always @(posedge clk, negedge rstn) begin
    if (!rstn) begin
      wptr <= 0;
    end else begin
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

  always @(posedge clk, negedge rstn) begin
    if (!rstn) begin
      rptr <= 0;
    end else begin
      if (rd_en & !empty) begin
        dout <= fifo[rptr];
        rptr <= rptr + 1;
      end
    end
  end

  assign full  = (wptr + 1) == rptr;
  assign empty = wptr == rptr;
endmodule