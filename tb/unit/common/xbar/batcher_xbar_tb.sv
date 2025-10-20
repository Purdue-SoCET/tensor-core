`timescale 1ns/1ns

`include "source/xbar_params.svh"
`include "source/xbar_if.sv"
`include "source/batcher_xbar.sv"

module batcher_xbar_tb;

  localparam int SIZE = 32;
  localparam int DWIDTH = 16;
  localparam int TAGW = $clog2(SIZE);
  localparam int LATENCY = (TAGW * (TAGW + 1)) / 2;  // 15 for SIZE=32
  localparam int N_REQS = 256;

  logic clk, n_rst;
  initial clk = 1'b0;
  always  #5 clk = ~clk;

  xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
  batcher_xbar #(.SIZE(SIZE), .DWIDTH(DWIDTH)) dut (xif);

  typedef logic [DWIDTH-1:0] vec_t [SIZE];
  vec_t exp_q[$];  // expected sorted vectors

  function automatic void make_vec(output vec_t v);
    for (int i = 0; i < SIZE; i++) v[i] = $urandom();
  endfunction

  function automatic void sort_vec(input vec_t in, output vec_t out);
    for (int i = 0; i < SIZE; i++) out[i] = in[i];
    for (int a = 0; a < SIZE-1; a++)
      for (int b = 0; b < SIZE-1-a; b++)
        if ($unsigned(out[b]) > $unsigned(out[b+1])) begin
          logic [DWIDTH-1:0] t = out[b];
          out[b]   = out[b+1];
          out[b+1] = t;
        end
  endfunction

  int launched, retired, errors;

  initial begin : main
    vec_t exp;                     
    logic [DWIDTH-1:0] got;      
    vec_t in_vec, exp_vec;

    n_rst = 1'b0;
    xif.en = 1'b0;
    for (int i = 0; i < SIZE; i++) begin
      xif.in[i].din = '0;
      xif.in[i].shift = TAGW'(i);  
    end
    repeat (5) @(posedge clk);
    n_rst = 1'b1;
    @(posedge clk);

    launched = 0;
    retired  = 0;
    errors = 0;

    // Stream N_REQS requests: one full vector per cycle
    xif.en = 1'b1;
    for (int t = 0; t < N_REQS; t++) begin
      make_vec(in_vec);
      sort_vec(in_vec, exp_vec);
      exp_q.push_back(exp_vec);
      launched++;

      // Drive a request
      for (int i = 0; i < SIZE; i++) begin
        xif.in[i].din   = in_vec[i];
        xif.in[i].shift = TAGW'(i);
      end

      @(posedge clk);

      // Retire after pipeline fills
      if (launched > LATENCY) begin
        exp = exp_q.pop_front();
        for (int k = 0; k < SIZE; k++) begin
          got = xif.out[k];
          if (got !== exp[k]) begin
            errors++;
            $display("[TB][Mismatch] retire=%0d lane=%0d got=%0h exp=%0h @%0t", retired, k, got, exp[k], $time);
          end
        end
        retired++;
      end
    end

    // Stop driving & drain remaining pipeline
    xif.en = 1'b0;
    for (int i = 0; i < SIZE; i++) begin
      xif.in[i].din   = '0;
      xif.in[i].shift = TAGW'(i);
    end

    for (int d = 0; d < LATENCY; d++) begin
      @(posedge clk);
      if (exp_q.size() != 0) begin
        exp = exp_q.pop_front();
        for (int k = 0; k < SIZE; k++) begin
          got = xif.out[k];
          if (got !== exp[k]) begin
            errors++;
            $display("[TB][Mismatch] retire=%0d lane=%0d got=%0h exp=%0h @%0t", retired, k, got, exp[k], $time);
          end
        end
        retired++;
      end
    end
    $finish;
  end
endmodule

