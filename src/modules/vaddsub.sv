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
  localparam int SIG_W = FRAC_W + 1;
  localparam int GRS_W = 3;
  localparam int EXT_W = SIG_W + GRS_W;
  localparam int SUM_W = EXT_W + 1;

  fp16_t fp1, fp2;
  assign fp1 = vaddsubif.port_a;
  assign fp2 = vaddsubif.port_b;

  logic sign_a = fp1.sign;
  logic sign_b = vaddsubif.sub ? (~fp2.sign) : fp2.sign;

  //Helper Functions
  function automatic bit is_nan(fp16_t f);  return (f.exp==5'h1F) && (f.frac!=0); endfunction
  function automatic bit is_inf(fp16_t f);  return (f.exp==5'h1F) && (f.frac==0); endfunction
  function automatic bit is_zero(fp16_t f); return (f.exp==0)     && (f.frac==0); endfunction
  function automatic bit is_sub (fp16_t f); return (f.exp==0)     && (f.frac!=0); endfunction

  // DAZ
  function automatic logic [EXP_W-1:0] eff_exp_daz(fp16_t f);
    return (f.exp==0) ? 5'd0 : f.exp;
  endfunction

  // DAZ: subnormals become 0.frac == 0; normals use 1.frac
  function automatic logic [SIG_W-1:0] make_sig_daz(fp16_t f);
    if (f.exp==0)         return '0;                 // ±0 or subnormal → 0
    else                  return {1'b1, f.frac};     // normal
  endfunction

  // right-shift with sticky
  function automatic logic [EXT_W-1:0]
  rshift_sticky(input logic [EXT_W-1:0] x, input logic [EXP_W-1:0] shamt, output logic sticky);
    logic [EXT_W-1:0] y; logic tail;
    if (shamt==0)         begin y=x; sticky=1'b0; end
    else if (shamt>=EXT_W)begin y='0; sticky=|x; end
    else                  begin y=x>>shamt; tail=|x[shamt-1:0]; sticky=tail; end
    return y;
  endfunction

  // Leading Zero Count
  function automatic int unsigned lzc15(input logic [SUM_W-1:0] x);
    int unsigned c = SUM_W;
    for (int i =S UM_W - 1;i >= 0;i -- ) if (x[i]) begin c = (SUM_W -1 ) - i; break; end
    return c;
  endfunction

  // round-to-nearest-even for 11 bits mantissa
  function automatic logic [SIG_W-1:0]
  round_rne(input logic [SIG_W-1:0] sig, input logic g, input logic r, input logic s, output logic carry);
    logic inc = g & (r | s | sig[0]);   // ties-to-even
    {carry, round_rne} = sig + inc;
  endfunction

  // Valid Signals
  logic s1_v, s2_v;

  // Stage 1 Regs
  logic        s1_special;
  logic [15:0] s1_special_res;
  logic [SUM_W-1:0] s1_mag;      // adder magnitude result
  logic [EXP_W-1:0] s1_exp_r;    // exponent of larger operand
  logic             s1_sign_r;   // sign of result

  // Stage 1 Combination Signals
  logic        s1n_special;
  logic [15:0] s1n_special_res;
  logic [SUM_W-1:0] s1n_mag;
  logic [EXP_W-1:0] s1n_exp_r;
  logic             s1n_sign_r;

  always_comb begin

    s1n_special     = 1'b0;
    s1n_special_res = '0;
    s1n_mag         = '0;
    s1n_exp_r       = '0;
    s1n_sign_r      = 1'b0;

    // Special Cases For IEEE
    if (is_nan(fp1) || is_nan(fp2)) begin
      s1n_special     = 1'b1;
      s1n_special_res = {1'b0,5'h1F,10'b1_0000_0000};
    end
    else if (is_inf(fp1) && is_inf(fp2)) begin
      if (sign_a ^ sign_b) begin
        s1n_special     = 1'b1;
        s1n_special_res = {1'b0,5'h1F,10'b1_0000_0000}; // +Inf + -Inf → NaN
      end else begin
        s1n_special     = 1'b1;
        s1n_special_res = {sign_a,5'h1F,10'h000};       // same-sign Inf
      end
    end
    else if (is_inf(fp1)) begin
      s1n_special     = 1'b1;
      s1n_special_res = {sign_a,5'h1F,10'h000};
    end
    else if (is_inf(fp2)) begin
      s1n_special     = 1'b1;
      s1n_special_res = {sign_b,5'h1F,10'h000};
    end
    else begin
      // DAZ Subnormals = 0
      logic [SIG_W-1:0] m1 = make_sig_daz(fp1);
      logic [SIG_W-1:0] m2 = make_sig_daz(fp2);
      logic [EXT_W-1:0] M1 = {m1,{GRS_W{1'b0}}};
      logic [EXT_W-1:0] M2 = {m2,{GRS_W{1'b0}}};

      logic [EXP_W-1:0] e1 = eff_exp_daz(fp1);   // 0 for DAZ/zero, exp for normals
      logic [EXP_W-1:0] e2 = eff_exp_daz(fp2);

      // magnitude order (A is larger)
      logic swap = (e2 > e1) || ((e2 == e1) && (m2 > m1));
      logic [EXP_W-1:0] eA = swap ? e2 : e1;
      logic [EXP_W-1:0] eB = swap ? e1 : e2;
      logic [EXT_W-1:0] MA = swap ? M2 : M1;
      logic [EXT_W-1:0] MB = swap ? M1 : M2;
      logic             sA = swap ? sign_b : sign_a;
      logic             sB = swap ? sign_a : sign_b;

      logic [EXP_W-1:0] ediff = eA - eB;
      logic stickyB;
      logic [EXT_W-1:0] MBs = rshift_sticky(MB, ediff, stickyB);
      MBs[0] = MBs[0] | stickyB;

      // add/sub magnitudes
      logic [SUM_W-1:0] Aext = {1'b0, MA};
      logic [SUM_W-1:0] Bext = {1'b0, MBs};
      logic             add_op = (sA == sB);

      s1n_mag    = add_op ? (Aext + Bext) : (Aext - Bext);
      s1n_exp_r  = eA;
      s1n_sign_r = sA;
    end
  end

  // Register Stage 1 Outputs
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      s1_v           <= 1'b0;
      s1_special     <= 1'b0;
      s1_special_res <= '0;
      s1_mag         <= '0;
      s1_exp_r       <= '0;
      s1_sign_r      <= 1'b0;
    end else begin
      s1_v           <= vaddsubif.enable;
      s1_special     <= s1n_special;
      s1_special_res <= s1n_special_res;
      s1_mag         <= s1n_mag;
      s1_exp_r       <= s1n_exp_r;
      s1_sign_r      <= s1n_sign_r;
    end
  end

  // Stage 2: Normalize + RNE + FTZ + Pack Output
  logic [15:0] s2n_out;
  logic        s2n_ovf;

  always_comb begin
    s2n_out = '0;
    s2n_ovf = 1'b0;

    if (s1_special || !s1_v) begin
      s2n_out = s1_special ? s1_special_res : 16'd0;

    end else if (s1_mag == '0) begin
      // Cancellation Policy for FTZ = +0
      s2n_out = 16'd0;

    end else begin
      //Normalization
      logic [SUM_W-1:0] mag   = s1_mag;
      logic [EXP_W-1:0] exp_r = s1_exp_r;
      logic [SUM_W-1:0] norm;
      logic [EXP_W-1:0] exp_n;

      logic carry = mag[SUM_W-1];
      if (carry) begin
        logic tail = mag[0];
        norm  = mag >> 1;
        norm[0] = norm[0] | tail;
        exp_n = exp_r + 1;
      end else begin
        int unsigned lz = lzc15(mag);
        int target = SIG_W + GRS_W - 1;
        int msb    = (SUM_W-1) - lz;
        int shl    = target - msb;
        if (shl > 0) begin
          norm  = mag << shl;
          exp_n = (exp_r > shl) ? (exp_r - shl) : '0;
        end else if (shl < 0) begin
          norm  = mag >> (-shl);
          exp_n = exp_r + (-shl);
          logic tail = |mag[(-shl)-1:0];
          norm[0] = norm[0] | tail;
        end else begin
          norm  = mag;
          exp_n = exp_r;
        end
      end

      // Extract Significant Bit + GRS
      logic [SIG_W-1:0] sig11 = norm[GRS_W +: SIG_W];
      logic guard = norm[2];
      logic round = norm[1];
      logic sticky= norm[0];

      // RNE
      logic carry_up;
      logic [SIG_W-1:0] sig_rnd = round_rne(sig11, guard, round, sticky, carry_up);

      logic [EXP_W-1:0] exp_post = exp_n + (carry_up ? 1 : 0);
      logic [SIG_W-1:0] sig_post = carry_up ? {1'b1, {FRAC_W{1'b0}}} : sig_rnd;

      // FTZ Pack (No Subnormals on Output)
      if (exp_post >= 5'h1F) begin
        // Overflow = += Infinity
        s2n_out = {s1_sign_r, 5'h1F, 10'h000};
        s2n_ovf = 1'b1;
      end else if (exp_post == 0) begin
        // Subnormal = Output is 0 for FTZ
        s2n_out = 16'd0;
        s2n_ovf = 1'b0;
      end else begin
        // normal
        s2n_out = {s1_sign_r, exp_post, sig_post[FRAC_W-1:0]};
        s2n_ovf = 1'b0;
      end
    end
  end

  // Stage 2 Registered Values
  logic [15:0] s2_out;
  logic        s2_ovf;

  // Register Stage 2 Values
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

  // Final (Ouputs)
  assign vaddsubif.out      = s2_v ? s2_out : 16'd0;
  assign vaddsubif.overflow = s2_v ? s2_ovf : 1'b0;

endmodule