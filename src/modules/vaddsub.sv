`include "vector_types.vh"
`include "vector_if.vh"
`include "vaddsub_if.vh"

module vaddsub(
  input  logic              CLK, 
  input  logic              nRST,
  vaddsub_if.vaddsub        vaddsubif 
);

  import vector_pkg::*;

  localparam int EXP_W = 5;
  localparam int FRAC_W = 10;
  localparam int SIG_W  = FRAC_W + 1;
  localparam int GRS_W  = 3;
  localparam int EXT_W  = SIG_W + GRS_W;
  localparam int SUM_W  = EXT_W + 1;

  fp16_t fp1, fp2;
  assign fp1 = vaddsubif.port_a;
  assign fp2 = vaddsubif.port_b;

  logic sign_a, sign_b_eff;
  assign sign_a     = fp1.sign;
  assign sign_b_eff = vaddsubif.sub ? (~fp2.sign) : fp2.sign;

  // Helper Functions
  function automatic bit is_nan (fp16_t f);  return (f.exp==5'h1F) && (f.frac!=0); endfunction
  function automatic bit is_inf (fp16_t f);  return (f.exp==5'h1F) && (f.frac==0); endfunction
  function automatic bit is_zero(fp16_t f);  return (f.exp==0)     && (f.frac==0); endfunction
  function automatic bit is_sub (fp16_t f);  return (f.exp==0)     && (f.frac!=0); endfunction

  function automatic logic [EXP_W-1:0] eff_exp(fp16_t f);
    return (f.exp==0) ? 5'd1 : f.exp;
  endfunction

  // Build significand
  function automatic logic [SIG_W-1:0] make_sig(fp16_t f);
    if (is_zero(f))       return '0;               // 0.frac for +0/-0
    else if (is_sub(f))   return {1'b0, f.frac};   // subnormal: 0.frac
    else                  return {1'b1, f.frac};   // normal:    1.frac
  endfunction

  // right shift with sticky
  function automatic logic [EXT_W-1:0]
    rshift_sticky(input logic [EXT_W-1:0] x, input logic [EXP_W-1:0] shamt, output logic sticky);
    logic [EXT_W-1:0] y;
    logic [EXT_W-1:0] mask;
    if (shamt == 0) begin
      y      = x;
      sticky = 1'b0;
    end else if (shamt >= EXT_W) begin
      y      = '0;
      sticky = |x;
    end else begin
      y      = x >> shamt;
      mask   = {EXT_W{1'b1}} >> (EXT_W - shamt);
      sticky = |(x & mask);
    end
    return y;
  endfunction

  // Count leading zeros
  function automatic int unsigned lzc_sum(input logic [SUM_W-1:0] x);
    int unsigned c = SUM_W;
    for (int i=SUM_W-1; i>=0; i--) if (x[i]) begin c=(SUM_W-1)-i; break; end
    return c;
  endfunction

  function automatic logic [SIG_W-1:0]
    round_rne(input logic [SIG_W-1:0] sig, input logic g, input logic r, input logic s, output logic carry_o);
    logic inc = g & (r | s | sig[0]);   // round-to-nearest-even
    {carry_o, round_rne} = sig + inc;
  endfunction

  // Next State Signals
  logic        n_valid;
  logic [15:0] n_out;
  logic        n_ovf;

  // Single Stage Datapath
  always_comb begin
    
    // Build Allign temps
    logic [SIG_W-1:0] m1;
    logic [SIG_W-1:0] m2;
    logic [EXT_W-1:0] M1;
    logic [EXT_W-1:0] M2;
    logic [EXT_W-1:0] MA;
    logic [EXT_W-1:0] MB;
    logic [EXT_W-1:0] MBs;
    logic [EXP_W-1:0] e1;
    logic [EXP_W-1:0] e2;
    logic [EXP_W-1:0] eA;
    logic [EXP_W-1:0] eB;
    logic [EXP_W-1:0] ediff;
    logic             swap;
    logic             sA;
    logic             sB;
    logic             stickyB;

    // add/sub temps
    logic [SUM_W-1:0] Aext;
    logic [SUM_W-1:0] Bext;
    logic             add_op;
    logic [SUM_W-1:0] mag;
    logic [EXP_W-1:0] exp_r;
    logic             sign_r;

    // normalize temps
    logic [SUM_W-1:0] norm;
    logic [EXP_W-1:0] exp_n;
    logic             carry;
    logic             tail;
    int unsigned      lz;
    int               tgt;
    int               msb;
    int               shl;
    int               r_amt;
    logic [SUM_W-1:0] mask_sum;

    // round/pack temps
    logic [SIG_W-1:0] sig11;
    logic             guard;
    logic             round;
    logic             sticky;
    logic             carry_up;
    logic [SIG_W-1:0] sig_rnd;
    logic [EXP_W-1:0] exp_post;
    logic [SIG_W-1:0] sig_post;
    logic [FRAC_W-1:0] subf;

    // Defaults
    n_valid = vaddsubif.enable;
    n_out   = 16'd0;
    n_ovf   = 1'b0;

    // Special Cases
    if (is_nan(fp1) || is_nan(fp2)) begin
      n_out = {1'b0, 5'h1F, 10'b1_0000_0000};
    end else if (is_inf(fp1) && is_inf(fp2)) begin
      if (sign_a ^ sign_b_eff)
        n_out = {1'b0, 5'h1F, 10'b1_0000_0000}; // inf - inf = NaN
      else
        n_out = {sign_a, 5'h1F, 10'h000};       // same-sign inf
    end else if (is_inf(fp1)) begin
      n_out = {sign_a, 5'h1F, 10'h000};
    end else if (is_inf(fp2)) begin
      n_out = {sign_b_eff, 5'h1F, 10'h000};
    end else begin
      // Build Allign
      m1 = make_sig(fp1);
      m2 = make_sig(fp2);
      M1 = {m1, {GRS_W{1'b0}}};
      M2 = {m2, {GRS_W{1'b0}}};

      e1 = eff_exp(fp1);
      e2 = eff_exp(fp2);

      // choose larger magnitude as A
      swap = (e2 > e1) || ((e2 == e1) && (m2 > m1));
      eA   = swap ? e2 : e1;
      eB   = swap ? e1 : e2;
      MA   = swap ? M2 : M1;
      MB   = swap ? M1 : M2;

      sA   = swap ? sign_b_eff : sign_a;
      sB   = swap ? sign_a     : sign_b_eff;

      ediff = eA - eB;

      MBs = rshift_sticky(MB, ediff, stickyB);
      MBs[0] = MBs[0] | stickyB; // fold sticky into LSB

      Aext   = {1'b0, MA};
      Bext   = {1'b0, MBs};
      add_op = (sA == sB);

      mag    = add_op ? (Aext + Bext) : (Aext - Bext);
      exp_r  = eA;
      sign_r = sA;

      if (mag == '0) begin
        n_out = 16'd0; // +0
      end else begin
        // Normalize
        norm  = '0;
        exp_n = '0;

        carry = mag[SUM_W-1];
        if (carry) begin
          // shift right by 1
          tail   = mag[0];
          norm   = mag >> 1;
          norm[0]= norm[0] | tail;
          exp_n  = exp_r + 1;
        end else begin
          lz   = lzc_sum(mag);
          tgt  = SIG_W + GRS_W - 1;
          msb  = (SUM_W-1) - lz;
          shl  = tgt - msb;

          if (shl > 0) begin
            norm  = mag << shl;
            exp_n = (exp_r > shl) ? (exp_r - shl) : '0;
          end else if (shl < 0) begin
            r_amt = -shl;
            norm  = mag >> r_amt;
            if (r_amt >= SUM_W) begin
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

        // Round to Nearest Even
        sig11  = norm[GRS_W +: SIG_W];
        guard  = norm[2];
        round  = norm[1];
        sticky = norm[0];

        sig_rnd  = round_rne(sig11, guard, round, sticky, carry_up);
        exp_post = exp_n + (carry_up ? 1 : 0);
        sig_post = carry_up ? {1'b1, {FRAC_W{1'b0}}} : sig_rnd;

        // Pack
        if (exp_post >= 5'h1F) begin
          n_out = {sign_r, 5'h1F, 10'h000};
          n_ovf = 1'b1;
        end else if (exp_post == 0) begin
          subf  = sig_post[FRAC_W-1:0];
          n_out = (subf == 0) ? 16'd0 : {sign_r, 5'd0, subf};
          n_ovf = 1'b0;
        end else begin
          n_out = {sign_r, exp_post, sig_post[FRAC_W-1:0]};
          n_ovf = 1'b0;
        end
      end
    end
  end

  // Single Pipeline Register
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      vaddsubif.out      <= 16'd0;
      vaddsubif.overflow <= 1'b0;
    end else begin
      if (n_valid) begin
        vaddsubif.out      <= n_out;
        vaddsubif.overflow <= n_ovf;
      end else begin
        vaddsubif.out      <= 16'd0;
        vaddsubif.overflow <= 1'b0;
      end
    end
  end

endmodule