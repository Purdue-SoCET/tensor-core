`include "vector_types.vh"
`include "vector_if.vh"
`include "vaddsub_if.vh"

module vaddsub(
  input  logic              CLK, 
  input  logic              nRST,
  vaddsub_if.vaddsub        vaddsubif 
);

  import vector_pkg::*;

  localparam int EXP_W = 8;
  localparam int FRAC_W = 7;
  localparam int SIG_W = FRAC_W + 1;
  localparam int GRS_W = 3;
  localparam int EXT_W = SIG_W + GRS_W;
  localparam int SUM_W = EXT_W + 1;
  localparam int SHL_W = ($clog2(SUM_W)+1);

  // Stage 1 temps
  logic [SIG_W-1:0] m1, m2;
  logic [EXT_W-1:0] M1, M2;
  logic [EXP_W-1:0] e1, e2;
  logic             swap;
  logic [EXP_W-1:0] eA, eB;
  logic [EXT_W-1:0] MA, MB;
  logic             sA, sB;
  logic [EXP_W-1:0] ediff;
  logic             stickyB;
  logic [EXT_W-1:0] MBs;
  logic [SUM_W-1:0] Aext, Bext;
  logic             add_op;

  // Stage 2 temps
  logic [SUM_W-1:0] mag, norm;
  logic [EXP_W-1:0] exp_r, exp_n;
  logic             carry;
  logic             tail;
  logic [$clog2(SUM_W+1)-1:0] lz;    // [3:0] for SUM_W=15
  logic [$clog2(SUM_W)-1:0]   target;// [3:0], holds 13
  logic [$clog2(SUM_W)-1:0]   msb;   // [3:0], 0..14
  logic signed [SHL_W-1:0] shl;  // signed, covers -1..13
  logic [$clog2(SUM_W+1)-1:0] r_amt; // [3:0], 0..1 (future-proof)             // used when shl < 0
  logic [SUM_W-1:0] mask_sum;              // variable mask for SUM_W-width
  logic [SIG_W-1:0] sig11;
  logic             guard, round, sticky;
  logic             carry_up;
  logic [SIG_W-1:0] sig_rnd;
  logic [EXP_W-1:0] exp_post;
  logic [SIG_W-1:0] sig_post;
  logic [FRAC_W-1:0] subf;                 // moved here (was declared in a branch)
  logic [EXP_W-1:0] shl_exp;  // zero-extended | truncated version of shl

  generate
    if (EXP_W >= SHL_W) begin
        assign shl_exp = {{(EXP_W-SHL_W){1'b0}}, $unsigned(shl)};
    end else begin
        assign shl_exp = $unsigned(shl[EXP_W-1:0]);
    end
  endgenerate


//   fp16_t fp1, fp2; //declaring the fp16 types
//   assign fp1 = vaddsubif.port_a;
//   assign fp2 = vaddsubif.port_b;
  logic [15:0] a = vaddsubif.port_a;
  logic [15:0] b = vaddsubif.port_b;
  localparam int TOTAL_W = 16;
  
  function automatic logic                 get_sign(input logic [TOTAL_W-1:0] x); return x[TOTAL_W-1]; endfunction
  function automatic logic [EXP_W-1:0]     get_exp (input logic [TOTAL_W-1:0] x); return x[FRAC_W+EXP_W-1 -: EXP_W]; endfunction
  function automatic logic [FRAC_W-1:0]    get_frac(input logic [TOTAL_W-1:0] x); return x[FRAC_W-1:0]; endfunction
  
  logic sign_a;
  logic sign_b;
  assign sign_a = get_sign(a);
  assign sign_b = vaddsubif.sub ? ~get_sign(b) : get_sign(b);

  //Helper Functions
  localparam logic [EXP_W-1:0] EXP_ALL1 = {EXP_W{1'b1}};
  function automatic bit is_nan (input logic [15:0] x); return (get_exp(x)==EXP_ALL1) && (get_frac(x)!='0); endfunction
  function automatic bit is_inf (input logic [15:0] x); return (get_exp(x)==EXP_ALL1) && (get_frac(x)=='0); endfunction
  function automatic bit is_zero(input logic [15:0] x); return (get_exp(x)=='0)       && (get_frac(x)=='0); endfunction
  function automatic bit is_sub (input logic [15:0] x); return (get_exp(x)=='0)       && (get_frac(x)!='0); endfunction

  // DAZ: subnormals act as zero
  function automatic logic [EXP_W-1:0] eff_exp(input logic [15:0] x); return (get_exp(x)=='0) ? '0 : get_exp(x); endfunction
  function automatic logic [SIG_W-1:0] make_sig(input logic [15:0] x);
    if (is_zero(x) || is_sub(x)) return '0;
    else                         return {1'b1, get_frac(x)};
  endfunction

  // right-shift with sticky (no variable part-selects)
  function automatic logic [EXT_W-1:0]
    rshift_sticky(input logic [EXT_W-1:0] x, input logic [EXP_W-1:0] shamt, output logic sticky);
    logic [EXT_W-1:0] y;
    logic [EXT_W-1:0] mask;   // lower shamt bits set
    if (shamt == 0) begin
      y      = x;
      sticky = 1'b0;
    end else if (shamt>=EXT_W) begin
      y      = '0;
      sticky = |x;
    end else begin
      y      = x >> shamt;
      // mask = (1<<shamt)-1 across EXT_W bits
      mask   = {EXT_W{1'b1}} >> (EXT_W - shamt);
      sticky = |(x & mask);
    end
    return y;
  endfunction

  function automatic logic [$clog2(SUM_W+1)-1:0] lzc (input logic [SUM_W-1:0] x);
    logic found; lzc = SUM_W[$clog2(SUM_W+1)-1:0]; found=1'b0;
    for (int i=SUM_W-1; i>=0; i--) if (!found && x[i]) begin lzc = (SUM_W-1)-i; found=1'b1; end
  endfunction

  function automatic logic [SIG_W-1:0]
      round_rne(input logic [SIG_W-1:0] sig, input logic g, input logic r, input logic s, output logic carry_o);
      logic inc = g & (r | s | sig[0]);   // ties-to-even
      {carry_o, round_rne} = sig + inc;
  endfunction

  // Pipeline Valid Signals
  logic s1_v, s2_v;

  // Stage 1 Registers
  logic             s1_special; //special case flag
  logic [15:0]      s1_special_res; //pre-computed special case result
  logic [SUM_W-1:0] s1_mag; // the magnitude result after add/sub
  logic [EXP_W-1:0] s1_exp_r; //exponent of larger magnitude operand
  logic             s1_sign_r; //result sign

  //Stage 1: Classification and Alignment
  logic             s1n_special;
  logic [15:0]      s1n_special_res;
  logic [SUM_W-1:0] s1n_mag;
  logic [EXP_W-1:0] s1n_exp_r;
  logic             s1n_sign_r;

  // Special Case Handling
  always_comb begin
    s1n_special     = 1'b0;
    s1n_special_res = '0;
      //NaN case
    if (is_nan(a) || is_nan(b)) begin
        s1n_special     = 1'b1;
        s1n_special_res = {1'b0, EXP_ALL1, {1'b1, {(FRAC_W-1){1'b0}}}}; // quiet NaN
    end else if (is_inf(a) && is_inf(b)) begin
        if (sign_a ^ sign_b) begin
            s1n_special     = 1'b1;
            s1n_special_res = {1'b0, EXP_ALL1, {1'b1, {(FRAC_W-1){1'b0}}}}; // NaN
        end else begin
            s1n_special     = 1'b1;
            s1n_special_res = {sign_a, EXP_ALL1, {FRAC_W{1'b0}}};           // ±Inf
        end
    end else if (is_inf(a)) begin
        s1n_special     = 1'b1;
        s1n_special_res = {sign_a, EXP_ALL1, {FRAC_W{1'b0}}};
    end else if (is_inf(b)) begin
        s1n_special     = 1'b1;
        s1n_special_res = {sign_b, EXP_ALL1, {FRAC_W{1'b0}}};
    end
  end

  // Magnitude Compare and Allignment
  always_comb begin
    // Initialize outputs (unchanged from your code)
    s1n_mag   = '0; 
    s1n_exp_r = '0; 
    s1n_sign_r= 1'b0;

    // Initialize temps moved to top (kept behavior)
    m1='0; m2='0; M1='0; M2='0;
    e1='0; e2='0; eA='0; eB='0; ediff='0;
    MA='0; MB='0; MBs='0;
    swap=1'b0; sA=1'b0; sB=1'b0; stickyB=1'b0;
    Aext='0; Bext='0; add_op=1'b0;

    if (!s1n_special) begin
      // Build full significands with hidden bits and GRS room
      m1 = make_sig(a);
      m2 = make_sig(b);
      M1 = {m1,{GRS_W{1'b0}}};
      M2 = {m2,{GRS_W{1'b0}}};

      e1 = eff_exp(a);
      e2 = eff_exp(b);

      // Decide which operand has the larger magnitude
      swap = (e2 > e1) || ((e2 == e1) && (m2 > m1));

      eA = swap ? e2 : e1;     // exponent of larger operand
      eB = swap ? e1 : e2;     // smaller exponent
      MA = swap ? M2 : M1;     // larger significand
      MB = swap ? M1 : M2;     // smaller significand
      sA = swap ? sign_b : sign_a; // larger sign
      sB = swap ? sign_a : sign_b; // smaller sign

      // Align smaller operand’s mantissa to larger exponent, track sticky
      ediff = eA - eB;
      MBs   = rshift_sticky(MB, ediff, stickyB);
      MBs[0]= MBs[0] | stickyB; // fold sticky into final bit

      // add/sub magnitudes
      Aext   = {1'b0, MA};
      Bext   = {1'b0, MBs};
      add_op = (sA == sB);

      s1n_mag    = add_op ? (Aext + Bext) : (Aext - Bext);
      s1n_exp_r  = eA;
      s1n_sign_r = sA;
    end
  end

  //Register Stage 1 Outputs
  always_ff @(posedge CLK or negedge nRST) begin
      if (!nRST) begin
          s1_v           <= '0;
          s1_special     <= '0;      
          s1_special_res <= '0;
          s1_mag         <= '0;             
          s1_exp_r       <= '0;             
          s1_sign_r      <= '0;
      end else begin
          s1_v           <= vaddsubif.enable;
          s1_special     <= s1n_special;
          s1_special_res <= s1n_special_res;
          s1_mag         <= s1n_mag;
          s1_exp_r       <= s1n_exp_r;
          s1_sign_r      <= s1n_sign_r;
      end
  end

  // Stage 2: Normalize, Round, and Pack

  logic [15:0] s2_out;
  logic        s2_ovf;

  // (Keeping your comment text as-is below)
  logic [15:0] s2n_out; 
  logic        s2n_ovf;

  always_comb begin
      s2n_out = '0;
      s2n_ovf = 1'b0;

      if (s1_special || !s1_v) begin
          s2n_out = s1_special ? s1_special_res : '0;
      end else if (s1_mag == '0) begin
          s2n_out = {1'b0, 5'd0, 10'd0};
      end else begin
          // Normalization
          mag   = s1_mag;
          exp_r = s1_exp_r;
          norm  = '0;
          exp_n = '0;

          carry = mag[SUM_W-1];
          if (carry) begin
              // Right shift 1, OR the dropped LSB into sticky
              tail  = mag[0];
              norm  = mag >> 1;
              norm[0] = norm[0] | tail;
              exp_n = exp_r + 1;
          end else begin
              // Left/right normalize using LZC and a single shift
              lz     = lzc(mag);
              target = SIG_W + GRS_W - 1; 
              msb    = (SUM_W-1) - lz;
              shl = $signed({1'b0, target}) - $signed({1'b0, msb});

              if (shl > 0) begin
                  norm  = mag << shl;
                  exp_n = (exp_r > shl_exp) ? (exp_r - shl_exp) : '0;
              end else if (shl < 0) begin
                  r_amt = $unsigned(-shl);
                  norm  = mag >> r_amt;
                  // tail = OR of the bits shifted out on the right
                  if (r_amt >= SUM_W[$clog2(SUM_W+1)-1:0]) begin
                    tail = |mag;
                  end else begin
                    mask_sum = {SUM_W{1'b1}} >> (SUM_W - r_amt);
                    tail     = |(mag & mask_sum);
                  end
                  norm[0] = norm[0] | tail;
                  exp_n   = exp_r + r_amt;
              end else begin
                  norm  = mag;
                  exp_n = exp_r;
              end
          end

          sig11  = norm[GRS_W +: SIG_W];
          guard  = norm[2];
          round  = norm[1];
          sticky = norm[0];

          carry_up = 1'b0;
          sig_rnd  = round_rne(sig11, guard, round, sticky, carry_up);

          exp_post = exp_n + (carry_up ? 1 : 0);
          sig_post = carry_up ? {1'b1, {FRAC_W{1'b0}}} : sig_rnd;

          if (exp_post >= EXP_ALL1) begin
            s2n_out = {s1_sign_r, EXP_ALL1, {FRAC_W{1'b0}}};
            s2n_ovf = 1'b1;
          end else if (exp_post == '0) begin
          // FTZ, as you coded:
            s2n_out = {s1_sign_r, {EXP_W{1'b0}}, {FRAC_W{1'b0}}};
            s2n_ovf = 1'b0;
          end else begin
            s2n_out = {s1_sign_r, exp_post, sig_post[FRAC_W-1:0]};
            s2n_ovf = 1'b0;
          end
      end
  end

  // Register Stage 2 Outputs (final)
  always_ff @(posedge CLK or negedge nRST) begin
      if (!nRST) begin
          s2_v   <= 1'b0;
          s2_out <= '0;
          s2_ovf <= 1'b0;
      end else begin
          s2_v   <= s1_v;        // valid propagates forward
          s2_out <= s2n_out;
          s2_ovf <= s2n_ovf;
      end
  end

  // Final Outputs
  assign vaddsubif.out      = s2_v ? s2_out : 16'b0;
  assign vaddsubif.overflow = s2_v ? s2_ovf : 1'b0;

endmodule