//By            : myles !!!! !
//Last updated  : October 2025 - 2 cycle FP16 adder with simple ports (no interfaces)

`timescale 1ns/1ps

module vaddsubmyles(
  input  logic        CLK, 
  input  logic        nRST,
  input  logic        enable,
  input  logic [15:0] port_a,
  input  logic [15:0] port_b,
  output logic [15:0] out,
  output logic        overflow,
  output logic        out_valid
);
 // i can prolly remove the subnormal stuff later 
  localparam int EXP_W = 5;
  localparam int FRAC_W = 10;
  localparam int SIG_W = FRAC_W + 1;
  localparam int GRS_W = 3;
  localparam int EXT_W = SIG_W + GRS_W;
  localparam int SUM_W = EXT_W + 1;

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
  int unsigned      lz;
  int               target;
  int               msb;
  int               shl;
  int               r_amt;
  logic [SUM_W-1:0] mask_sum;
  logic [SIG_W-1:0] sig11;
  logic             guard, round, sticky;
  logic             carry_up;
  logic [SIG_W-1:0] sig_rnd;
  logic [EXP_W-1:0] exp_post;
  logic [SIG_W-1:0] sig_post;
  logic [FRAC_W-1:0] subf;

  // FP16 structure helpers
  logic        sign_a, sign_b;
  logic [4:0]  exp_a, exp_b;
  logic [9:0]  frac_a, frac_b;
  
  assign sign_a = port_a[15];
  assign exp_a  = port_a[14:10];
  assign frac_a = port_a[9:0];
  
  assign sign_b = port_b[15];
  assign exp_b  = port_b[14:10];
  assign frac_b = port_b[9:0];

  //Helper Functions
  function automatic bit is_nan_a();  return (exp_a==5'h1F) && (frac_a!=0); endfunction
  function automatic bit is_nan_b();  return (exp_b==5'h1F) && (frac_b!=0); endfunction
  function automatic bit is_inf_a();  return (exp_a==5'h1F) && (frac_a==0); endfunction
  function automatic bit is_inf_b();  return (exp_b==5'h1F) && (frac_b==0); endfunction
  function automatic bit is_zero_a(); return (exp_a==0)     && (frac_a==0); endfunction
  function automatic bit is_zero_b(); return (exp_b==0)     && (frac_b==0); endfunction
  function automatic bit is_sub_a();  return (exp_a==0)     && (frac_a!=0); endfunction
  function automatic bit is_sub_b();  return (exp_b==0)     && (frac_b!=0); endfunction

  // Effective exponent (subnormals act like exp=1 for alignment)
  function automatic logic [EXP_W-1:0] eff_exp_a(); return (exp_a==0) ? 5'd1 : exp_a; endfunction
  function automatic logic [EXP_W-1:0] eff_exp_b(); return (exp_b==0) ? 5'd1 : exp_b; endfunction
  
  // Build significand: hidden=1 for normals, 0 for subnormals
  function automatic logic [SIG_W-1:0] make_sig_a();
      if (is_zero_a())       return '0;
      else if (is_sub_a())   return {1'b0, frac_a};
      else                   return {1'b1, frac_a};
  endfunction
  
  function automatic logic [SIG_W-1:0] make_sig_b();
      if (is_zero_b())       return '0;
      else if (is_sub_b())   return {1'b0, frac_b};
      else                   return {1'b1, frac_b};
  endfunction

  // right-shift with sticky
  function automatic logic [EXT_W-1:0]
    rshift_sticky(input logic [EXT_W-1:0] x, input logic [EXP_W-1:0] shamt, output logic sticky);
    logic [EXT_W-1:0] y;
    logic [EXT_W-1:0] mask;
    if (shamt == 0) begin
      y      = x;
      sticky = 1'b0;
    end else if (shamt>=EXT_W) begin
      y      = '0;
      sticky = |x;
    end else begin
      y      = x >> shamt;
      mask   = {EXT_W{1'b1}} >> (EXT_W - shamt);
      sticky = |(x & mask);
    end
    return y;
  endfunction

  function automatic int unsigned lzc15(input logic [SUM_W-1:0] x);
      int unsigned c = SUM_W;
      for (int i=SUM_W-1;i>=0;i--) if (x[i]) begin c=(SUM_W-1)-i; break; end
      return c;
  endfunction

  function automatic logic [SIG_W-1:0]
      round_rne(input logic [SIG_W-1:0] sig, input logic g, input logic r, input logic s, output logic carry_o);
      logic inc = g & (r | s | sig[0]);
      {carry_o, round_rne} = sig + inc;
  endfunction

  // Pipeline Valid Signals
  logic s1_v, s2_v;

  // Stage 1 Registers
  logic             s1_special;
  logic [15:0]      s1_special_res;
  logic [SUM_W-1:0] s1_mag;
  logic [EXP_W-1:0] s1_exp_r;
  logic             s1_sign_r;

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
      if (is_nan_a() || is_nan_b()) begin
          s1n_special     = 1'b1;
          s1n_special_res = {1'b0,5'h1F,10'b1_0000_0000};
      end 
      //Infinity Case
      else if (is_inf_a() && is_inf_b()) begin
          if (sign_a ^ sign_b) begin
              // Infinity + (-Infinity) = NaN
              s1n_special     = 1'b1;
              s1n_special_res = {1'b0,5'h1F,10'b1_0000_0000};
          end else begin
              // same-sign Inf ± Inf = Same Infinity
              s1n_special     = 1'b1;
              s1n_special_res = {sign_a,5'h1F,10'h000};
          end
      end 
      // Other Infinity Case (Infinity Dominates)
      //Infinity + x = Infinity
      else if (is_inf_a()) begin
          s1n_special     = 1'b1;
          s1n_special_res = {sign_a,5'h1F,10'h000};
      end 
      //x + Infinity = Infinity 
      else if (is_inf_b()) begin
          s1n_special     = 1'b1;
          s1n_special_res = {sign_b,5'h1F,10'h000};
      end
  end

  // Magnitude Compare and Alignment
  always_comb begin
    s1n_mag   = '0; 
    s1n_exp_r = '0; 
    s1n_sign_r= 1'b0;

    m1='0; m2='0; M1='0; M2='0;
    e1='0; e2='0; eA='0; eB='0; ediff='0;
    MA='0; MB='0; MBs='0;
    swap=1'b0; sA=1'b0; sB=1'b0; stickyB=1'b0;
    Aext='0; Bext='0; add_op=1'b0;

    if (!s1n_special) begin
      // Build full significands with hidden bits and GRS room
      m1 = make_sig_a();
      m2 = make_sig_b();
      M1 = {m1,{GRS_W{1'b0}}};
      M2 = {m2,{GRS_W{1'b0}}};

      e1 = eff_exp_a();
      e2 = eff_exp_b();

      // Decide which operand has the larger magnitude
      swap = (e2 > e1) || ((e2 == e1) && (m2 > m1));

      eA = swap ? e2 : e1;
      eB = swap ? e1 : e2;
      MA = swap ? M2 : M1;
      MB = swap ? M1 : M2;
      sA = swap ? sign_b : sign_a;
      sB = swap ? sign_a : sign_b;

      // Align smaller operand's mantissa to larger exponent, track sticky
      ediff = eA - eB;
      MBs   = rshift_sticky(MB, ediff, stickyB);
      MBs[0]= MBs[0] | stickyB;

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
          s1_v           <= enable;
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

  logic [15:0] s2n_out; 
  logic        s2n_ovf;

  always_comb begin
      s2n_out = '0;
      s2n_ovf = 1'b0;

      if (s1_special || !s1_v) begin
          s2n_out = s1_special ? s1_special_res : 16'd0;
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
              tail  = mag[0];
              norm  = mag >> 1;
              norm[0] = norm[0] | tail;
              exp_n = exp_r + 1;
          end else begin
              lz     = lzc15(mag);
              target = SIG_W + GRS_W - 1; 
              msb    = (SUM_W-1) - lz;
              shl    = target - msb;

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

          sig11  = norm[GRS_W +: SIG_W];
          guard  = norm[2];
          round  = norm[1];
          sticky = norm[0];

          carry_up = 1'b0;
          sig_rnd  = round_rne(sig11, guard, round, sticky, carry_up);

          exp_post = exp_n + (carry_up ? 1 : 0);
          sig_post = carry_up ? {1'b1, {FRAC_W{1'b0}}} : sig_rnd;

          if (exp_post >= 5'h1F) begin
              // Overflow = ±Inf
              s2n_out = {s1_sign_r, 5'h1F, 10'h000};
              s2n_ovf = 1'b1;
          end else if (exp_post == 0) begin
              // Subnormal or zero: drop hidden bit
              subf    = sig_post[FRAC_W-1:0];
              s2n_out = (subf == 0) ? {1'b0, 5'd0, 10'd0} : {s1_sign_r, 5'd0, subf};
              s2n_ovf = 1'b0;
          end else begin
              // Normal
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
          s2_v   <= s1_v;
          s2_out <= s2n_out;
          s2_ovf <= s2n_ovf;
      end
  end

  // Final Outputs
  assign out      = s2_out;
  assign overflow = s2_ovf;
  assign out_valid = s2_v;

endmodule
