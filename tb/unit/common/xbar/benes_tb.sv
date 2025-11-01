// // `timescale 1ns / 1ns

// // module benes_tb;
// //     localparam int PERIOD = 10;
// //     localparam int SIZE = 32;
// //     localparam int DWIDTH = 16;
// //     localparam int TAGWIDTH = $clog2(SIZE);
// //     localparam int STAGES = (2 * TAGWIDTH) - 1;
// //     localparam int BITWIDTH = STAGES * (SIZE >> 1);

// //     logic clk, n_rst;
// //     logic [BITWIDTH-1:0] control_bit ;

// //     initial clk = 1'b0;
// //     always  #5 clk = ~clk;
    
// //     xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
// //     benes #(.SIZE(SIZE), .DWIDTH(DWIDTH)) DUT (xif, control_bit);

// //     integer i;
// //     logic [15:0] val;
// //     logic [DWIDTH-1:0] exp_out [SIZE-1:0];

// //     // REQUIRED FOR TESTING WITH CBG

// //     // typedef logic [DWIDTH-1:0] vec_t [SIZE];
// //     // vec_t in, exp_out;

// //     // function automatic void make_vec(output logic [TAGW-1:0] exp_out [SIZE-1:0]);
// //     //     logic [DWIDTH-1:0] idx [SIZE-1:0];
// //     //     logic [DWIDTH-1:0] tmp;
// //     //     integer i, j, tmp;

// //     //     for (i = 0; i < 32; i++)
// //     //     idx[i] = i;

// //     //     for (i = 31; i > 0; i--) begin
// //     //         j = $urandom_range(0, i); // random index to swap
// //     //         tmp = idx[i];
// //     //         idx[i] = idx[j];
// //     //         idx[j] = tmp;
// //     //     end

// //     //     for (i = 0; i < 32; i++)
// //     //         exp_out[i] = idx[i];

// //     // endfunction

// // initial begin
// //     n_rst = 0;

// //     #(PERIOD);

// //     n_rst = 1;
// //     val = 16'd0;

// //     for (i = 0; i < 32; i = i + 1) begin
// //         xif.in[i] = val;
// //         val = val + 16'd1;
// //     end
// //     exp_out = {16'd27, 16'd24, 16'd2, 16'd29, 16'd4, 16'd7, 16'd20, 16'd10, 16'd1, 16'd0, 16'd8, 16'd9, 16'd3, 16'd13, 16'd16, 16'd26,
// //                     16'd12, 16'd31, 16'd17, 16'd19, 16'd28, 16'd18, 16'd23, 16'd30, 16'd5, 16'd15, 16'd6, 16'd21, 16'd11, 16'd25, 16'd22, 16'd14};
    
// //     control_bit = 144'b111000110101110001100100110011100111001110000000111100000001101100101011001100000000000000000000001000011001000001110110011110001011111001001100;  
    
// //     repeat (10) #(PERIOD);
    
// //     for (i = 0; i < 32; i = i + 1) begin
// //         if(xif.out[i] != exp_out[(SIZE-1 - i)]) begin
// //             $display("wrong output for %d", i);
// //         end
// //         // $display("output %d: %d", i, xif.out[i]);
// //     end
// //     $finish;
// // end

// // endmodule













`timescale 1ns/1ns

`include "xbar_params.svh"
`include "xbar_if.sv"

module benes_sort_tb;

  import xbar_pkg::*;

  localparam int SIZE = 32;
  localparam int DWIDTH = 16;
  localparam int TAGW = $clog2(SIZE);
  localparam int STAGES = (2*TAGW) - 1;
  localparam logic [STAGES-2:0] REGISTER_MASK = 8'b11111111;
  localparam int REAL_LATENCY = $countones(REGISTER_MASK) + 1;

  localparam int N_REQS = (REAL_LATENCY * 2);
  localparam int VERBOSE = 0;

  logic clk, n_rst;
  initial clk = 1'b0;
  always  #5 clk = ~clk;

  xbar_if #(.SIZE(SIZE), .DWIDTH(DWIDTH)) xif (.clk(clk), .n_rst(n_rst));
  benes #(.SIZE(SIZE), .DWIDTH(DWIDTH), .REGISTER_MASK(REGISTER_MASK)) dut (.xif(xif.xbar));

  typedef logic [DWIDTH-1:0] vec_t [SIZE];
  vec_t exp_q[$];

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
    xif.en  = 1'b0;
    for (int i = 0; i < SIZE; i++) begin
      xif.in[i].din = '0;
      xif.in[i].shift = TAGW'(i); // tag each lane (debug)
    end
    repeat (5) @(posedge clk);
    n_rst = 1'b1;
    @(posedge clk);

    launched = 0;
    retired = 0;
    errors = 0;
    xif.en = 1'b1;

    for (int t = 0; t < N_REQS; t++) begin
      // Launch until pipeline is filled
      if (launched <= REAL_LATENCY) begin
        make_vec(in_vec); // random input
        sort_vec(in_vec, exp_vec); // sorted output
        exp_q.push_back(exp_vec); // remember for later comparison
        launched++;

        // Drive a single request (one full vector)
        for (int i = 0; i < SIZE; i++) begin
          xif.in[i].din = in_vec[i];
          xif.in[i].shift = TAGW'(i);
        end
      end

      @(posedge clk);
      // Start retiring after latency
      if (launched >= REAL_LATENCY) begin
        exp = exp_q.pop_front();
        mismatches = 0;

        for (int k = 0; k < SIZE; k++) begin
          got = xif.out[k];
          if (got !== exp[k]) begin
            mismatches++;
            errors++;
            $display($sformatf("[BENES][lane%0d] got=%0d exp=%0d", k, got, exp[k]));
          end else if (VERBOSE) begin
            $display($sformatf("[BENES][lane%0d] got=%0d exp=%0d", k, got, exp[k]));
          end
        end

        if (mismatches == 0) begin
          $display("[BENES][Complete] retire=%0d OK", retired);
        end else begin
          $display("[BENES][Complete] retire=%0d mismatches=%0d", retired, mismatches);
        end
        retired++;
      end
    end

    // Stop driving
    xif.en = 1'b0;

    $display("[BENES][Summary] errors=%0d (latency=%0d)", errors, REAL_LATENCY);
    $finish;
  end

endmodule
