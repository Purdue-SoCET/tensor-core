`timescale 1ns/1ns

`include "xbar_params.svh"
`include "xbar_if.sv"

module batcher_tb;

  import xbar_pkg::*;

  // Don't change for this testbench. REGISTER_MASKs can only get used for SIZE = 32. 
  // Read xbar_pkg.sv notes, if you want to understand more. 
  localparam int SIZE = 32; 

  localparam int DWIDTH = 16;
  localparam int TAGW = $clog2(SIZE);
  localparam int STAGES = (TAGW * (TAGW + 1)) / 2;

  localparam logic [STAGES-2:0] REGISTER_MASK = BA_INTO_3;
  localparam int REAL_LATENCY = $countones(REGISTER_MASK) + 1; 

  localparam int N_REQS = (REAL_LATENCY * 2);
  localparam int VERBOSE  = 0;

  logic clk, n_rst;
  initial clk = 1'b0;
  always  #5 clk = ~clk;

  xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
  batcher #(.SIZE(SIZE), .DWIDTH(DWIDTH), .REGISTER_MASK(REGISTER_MASK)) dut (.xif(xif.xbar));

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
  int mismatches;
  string lanes;

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

    xif.en = 1'b1;
    // Steam all stages and fill up. 
    for (int t = 0; t < N_REQS; t++) begin
      // Retire after pipeline fills
      if (launched <= REAL_LATENCY) begin
        make_vec(in_vec);
        sort_vec(in_vec, exp_vec);
        exp_q.push_back(exp_vec);
        launched++;

        // Drive a request
        for (int i = 0; i < SIZE; i++) begin
          xif.in[i].din = in_vec[i];
          xif.in[i].shift = TAGW'(i);
        end
      end 

      @(posedge clk);

      // Retire after pipeline fills
      if (launched >= REAL_LATENCY) begin
        exp = exp_q.pop_front();
        mismatches = 0;

        for (int k = 0; k < SIZE; k++) begin
          got = xif.out[k];
          if (got !== exp[k]) begin
            mismatches++;
            errors++;
            $display($sformatf("lane%0d: got=%0d exp=%0d", k, got, exp[k]));
          end else if (VERBOSE) begin 
            $display($sformatf("lane%0d: got=%0d exp=%0d", k, got, exp[k]));
          end 
        end

        if (mismatches == 0) begin
          $display("[TB][Complete] retire=%0d OK", retired);
        end else begin
          $display("[TB][Complete] retire=%0d mismatches=%0d", retired, mismatches);
        end

        retired++;
      end
    end

    // stop driving; no drain needed
    xif.en = 1'b0;

    $display("[TB][Summary] errors=%0d", errors);
    $finish;
  end

endmodule

