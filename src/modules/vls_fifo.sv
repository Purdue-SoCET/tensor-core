module vls_fifo #(
  parameter int FIFODEPTH = 8,          // prefer power of two
  parameter int DATAWIDTH = 16
)(
  input  logic                 nRST,     // Active-low reset
  input  logic                 CLK,      // Clock
  input  logic                 wr_en,    // Write enable (push)
  input  logic                 shift,    // Read enable (pop)
  input  logic [DATAWIDTH-1:0] din,      // Data in
  output logic [DATAWIDTH-1:0] dout,     // Data out (registered)
  output logic                 empty,    // 1 when empty
  output logic                 full      // 1 when full (one-slot-empty scheme)
);
  localparam int AW = $clog2(FIFODEPTH);

  // Optional: assert that FIFODEPTH is power of two
  // synopsys translate_off
  initial begin
    if ((1<<AW) != FIFODEPTH)
      $error("sync_fifo: FIFODEPTH (%0d) must be a power of two for pointer wrap.", FIFODEPTH);
  end
  // synopsys translate_on

  logic [DATAWIDTH-1:0] mem [FIFODEPTH-1:0];
  logic [AW-1:0] wptr, rptr;

  // Next-pointer math (wrap is automatic with AW bits)
  logic [AW-1:0] wptr_n = wptr + 1'b1;
  logic [AW-1:0] rptr_n = rptr + 1'b1;

  // Status with one-slot-empty scheme (combinational, current pointers)
  assign empty = (wptr == rptr);
  assign full  = (wptr_n == rptr);

  // Improved enables to allow write on same-cycle read from full
  wire do_write = wr_en && (!full  || shift);   // if full but also shifting, allow write
  wire do_read  = shift && (!empty || wr_en);   // optional: allow read when empty but writing same cycle

  // Write port
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      wptr <= '0;
    end else begin
      if (do_write) begin
        mem[wptr] <= din;
        wptr      <= wptr_n;
      end
    end
  end

  // Read port + registered dout
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      rptr <= '0;
      dout <= '0;
    end else begin
      // present current head data each cycle (registered)
      dout <= mem[rptr];
      if (do_read) begin
        rptr <= rptr_n;
      end
    end
  end
endmodule