`include "scpad_params.svh"
`include "scpad_if.sv"

import scpad_pkg::*;

module sram_bank # ( 
  parameter int READ_LATENCY = 2, 
  parameter int WRITE_LATENCY = 4
) (
  input logic clk, n_rst, 

  output logic busy,

  input logic ren,
  input logic [ROW_IDX_WIDTH-1:0] raddr,
  output logic [ELEM_BITS-1:0] rdata,
  output logic rdone, 

  input logic wen,
  input logic [ROW_IDX_WIDTH-1:0] waddr,
  input logic [ELEM_BITS-1:0] wdata, 
  output logic wdone
);  
  import scpad_types_pkg::*;

  logic [NUM_ROWS-1:0][ELEM_BITS-1:0] mem;

  localparam int RLW = (READ_LATENCY <= 1) ? 1 : $clog2(READ_LATENCY);
  logic [RLW-1:0] r_cnt;
  logic  r_busy;
  localparam int WLW = (WRITE_LATENCY <= 1) ? 1 : $clog2(WRITE_LATENCY);
  logic [WLW-1:0] w_cnt;
  logic w_busy;

  assign busy = r_busy || w_busy; 

  always_ff @(posedge clk, negedge n_rst) begin
    if (!n_rst) begin
      r_busy <= 1'b0;
      r_cnt  <= '0;
      rdone  <= 1'b0;
    end else begin
      rdone <= 1'b0; 

      if (ren && !r_busy) begin
        r_busy <= 1'b1;
        r_cnt <= (READ_LATENCY <= 1) ? '0 : READ_LATENCY-1;
        if (READ_LATENCY <= 1) begin
          rdone <= 1'b1;
          r_busy <= 1'b0;
        end
      end else if (r_busy) begin
        if (r_cnt == '0) begin
          rdone <= 1'b1;
          r_busy <= 1'b0;
        end else begin
          r_cnt <= r_cnt - 1'b1;
        end
      end
    end
  end

  always_ff @(posedge clk, negedge n_rst) begin
    if (!n_rst) begin
      w_busy <= 1'b0;
      w_cnt  <= '0;
      wdone  <= 1'b0;
    end else begin
      wdone <= 1'b0; 

      if (wen && !w_busy) begin
        w_busy <= 1'b1;
        w_cnt <= (WRITE_LATENCY <= 1) ? '0 : WRITE_LATENCY-1;
        if (WRITE_LATENCY <= 1) begin
          wdone  <= 1'b1;
          w_busy <= 1'b0;
        end
      end else if (w_busy) begin
        if (w_cnt == '0) begin
          wdone  <= 1'b1;
          w_busy <= 1'b0;
        end else begin
          w_cnt <= w_cnt - 1'b1;
        end
      end
    end
  end

  always_ff @ (posedge clk, negedge n_rst) begin
    if (!n_rst) begin 
      mem <= '0; 
      rdata <= '0; 
    end else begin 
      if (ren) begin
        rdata <= mem[raddr];
      end
      if (wen) begin
        mem[waddr] <= wdata;
      end
    end
  end

endmodule
