`include "vector_types.vh"
`include "vector_if.vh"
`include "vaddsub_if.vh"
//need to add a control signal for the subtract module to flip the sign of the second input
module vaddsub(
    input logic CLK, 
    input logic nRST,
    vaddsub_if.vaddsub vaddsubif 
);

// importing vector types package
import vector_pkg::*;

fp16_t fp1, fp2; //declaring the fp16 types

localparam int EXP_W = 5, FRAC_W = 10, SIG_W = FRAC_W + 1, GRS_W = 3, EXT_W = SIG_W + GRS_W, SUM_W = EXT_W + 1;
logic sign_a;
logic sign_b;

//Helper Functions
function automatic bit is_nan(fp16_t f);  return (f.exp==5'h1F) && (f.frac!=0); endfunction
function automatic bit is_inf(fp16_t f);  return (f.exp==5'h1F) && (f.frac==0); endfunction
function automatic bit is_zero(fp16_t f); return (f.exp==0)     && (f.frac==0); endfunction
function automatic bit is_sub (fp16_t f); return (f.exp==0)     && (f.frac!=0); endfunction

// Effective exponent (subnormals act like exp=1 for alignment)
function automatic logic [EXP_W-1:0] eff_exp(fp16_t f); return (f.exp==0) ? 5'd1 : f.exp; endfunction
// Build significand: hidden=1 for normals, 0 for subnormals
function automatic logic [SIG_W-1:0] make_sig(fp16_t f);
    if (is_zero(f))       return '0;                 // 0.frac for +0 or -0
    else if (is_sub(f))   return {1'b0, f.frac};     // subnormal: 0.frac
    else                  return {1'b1, f.frac};     // normal:    1.frac
endfunction

function automatic logic [EXT_W-1:0]
    rshift_sticky(input logic [EXT_W-1:0] x, input logic [EXP_W-1:0] shamt, output logic sticky);
    logic [EXT_W-1:0] y; logic tail;
    if (shamt==0) begin y=x; sticky=1'b0; end
    else if (shamt>=EXT_W) begin y='0; sticky=|x; end
    else begin y=x>>shamt; tail=|x[shamt-1:0]; sticky=tail; end
    return y;
endfunction

function automatic int unsigned lzc15(input logic [SUM_W-1:0] x);
    int unsigned c = SUM_W;
    for (int i=SUM_W-1;i>=0;i--) if (x[i]) begin c=(SUM_W-1)-i; break; end
    return c;
endfunction

function automatic logic [SIG_W-1:0]
    round_rne(input logic [SIG_W-1:0] sig, input logic g, input logic r, input logic s, output logic carry);
    logic inc = g & (r | s | sig[0]);   // ties-to-even
    {carry, round_rne} = sig + inc;
endfunction

assign fp1 = vaddsubif.port_a;
assign fp2 = vaddsubif.port_b;
assign sign_a = fp1.sign;
assign sign_b = vaddsubif.sub ? (~fp2.sign) : fp2.sign;

// Pipeline Valid Signals
logic s1_v, s2_v, s3_v;

// Stage 1 Registers
logic             s1_special; //special case flag
logic [15:0]      s1_special_res; //pre-computed special case result
logic [EXT_W-1:0] s1_MA, s1_MB_algn; //larger and smaller operand mantissa after normalization
logic [EXP_W-1:0] s1_eA; //exponent of larger magnitude operand
logic             s1_add_op; //control bit for signifying addition or subtraction          
logic             s1_signA; //sign bit of larger magnitude operand          

// Stage 2 Registers
logic [SUM_W-1:0] s2_mag; // the magnitude result of addition/subtraction
logic [EXP_W-1:0] s2_exp_r; //stage 2 exponent result of the larger operand
logic             s2_sign_r; //result sign
logic             s2_special; //stage 2 special case flag
logic [15:0]      s2_special_res; //stage 2 special case result

// Stage 3 Registers
logic [15:0] s3_out; //final output result
logic        s3_ovf; //overflow flag

//Stage 1: Classification and Alignment
logic             s1n_special;
logic [15:0]      s1n_special_res;
logic [EXT_W-1:0] s1n_MA, s1n_MB_algn;
logic [EXP_W-1:0] s1n_eA;
logic             s1n_add_op, s1n_signA;

// Special Case Handling
always_comb begin
  s1n_special     = 1'b0;
  s1n_special_res = '0;
    //NaN case
    if (is_nan(fp1) || is_nan(fp2)) begin
        s1n_special     = 1'b1;
        s1n_special_res = {1'b0,5'h1F,10'b1_0000_0000};
    end 
    //Infinity Case
    else if (is_inf(fp1) && is_inf(fp2)) begin
        if (sign_a ^ sign_b) begin
            // Ifinity + (-Infinity) = NaN
            s1n_special     = 1'b1;
            s1n_special_res = {1'b0,5'h1F,10'b1_0000_0000};
        end else begin
            // same-sign Inf ± Inf = Same Infinity
            s1n_special     = 1'b1;
            s1n_special_res = {sign_a,5'h1F,10'h000};
        end
    end 
    // Other Infininity Case (Infinity Dominates)
    //Infinty + x = Infinity
    else if (is_inf(fp1)) begin
        s1n_special     = 1'b1;
        s1n_special_res = {sign_a,5'h1F,10'h000};
    end 
    //x + Infinity = Infinity 
    else if (is_inf(fp2)) begin
        s1n_special     = 1'b1;
        s1n_special_res = {sign_b,5'h1F,10'h000};
    end
end

// Magnitude Compare and Allignment
always_comb begin
  s1n_MA='0; s1n_MB_algn='0; s1n_eA='0; s1n_add_op=1'b0; s1n_signA=1'b0;

  if (!s1n_special) begin
    // Build full significands with hidden bits and GRS room
    logic [SIG_W-1:0] m1 = make_sig(fp1);
    logic [SIG_W-1:0] m2 = make_sig(fp2);
    logic [EXT_W-1:0] M1 = {m1,{GRS_W{1'b0}}};
    logic [EXT_W-1:0] M2 = {m2,{GRS_W{1'b0}}};

    logic [EXP_W-1:0] e1 = eff_exp(fp1);
    logic [EXP_W-1:0] e2 = eff_exp(fp2);

    // Decide which operand has the larger magnitude
    logic swap = (e2 > e1) || ((e2 == e1) && (m2 > m1));

    logic [EXP_W-1:0] eA = swap ? e2 : e1;     // exponent of larger operand
    logic [EXP_W-1:0] eB = swap ? e1 : e2;     // smaller exponent
    logic [EXT_W-1:0] MA = swap ? M2 : M1;     // larger significand
    logic [EXT_W-1:0] MB = swap ? M1 : M2;     // smaller significand
    logic             sA = swap ? sign_b : sign_a; // larger sign
    logic             sB = swap ? sign_a : sign_b; // smaller sign

    // Align smaller operand’s mantissa to larger exponent, track sticky
    logic [EXP_W-1:0] ediff = eA - eB;
    logic stickyB;
    logic [EXT_W-1:0] MBs = rshift_sticky(MB, ediff, stickyB);
    MBs[0] = MBs[0] | stickyB; // fold sticky into final bit

    // Populate outputs for Stage 2
    s1n_MA      = MA;
    s1n_MB_algn = MBs;
    s1n_eA      = eA;
    s1n_add_op  = (sA == sB); // add if same sign
    s1n_signA   = sA;         // result sign = sign of larger magnitude
  end
end

//Register Stage 1 Outputs
always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
        s1_v           <= '0;
        s1_special     <= '0;      
        s1_special_res <= '0;
        s1_MA          <= '0;             
        s1_MB_algn     <= '0;
        s1_eA          <= '0;             
        s1_add_op      <= '0;
        s1_signA       <= '0;
    end else begin
        s1_v           <= vaddsubif.enable;
        s1_special     <= s1n_special;
        s1_special_res <= s1n_special_res;
        s1_MA          <= s1n_MA;
        s1_MB_algn     <= s1n_MB_algn;
        s1_eA          <= s1n_eA;
        s1_add_op      <= s1n_add_op;
        s1_signA       <= s1n_signA;
    end
end

// Stage 2:
// Add and Subtract Magnitudes
logic [SUM_W-1:0] s2n_mag;
logic [EXP_W-1:0] s2n_exp_r;
logic             s2n_sign_r;
logic             s2n_special;
logic [15:0]      s2n_special_res;

always_comb begin
    // Pass-through of specials from S1
    s2n_special     = s1_special;
    s2n_special_res = s1_special_res;

    if (s1_special || !s1_v) begin
    // If Special Case or stage 1 enable is off, zero the stage 2 outputs
        s2n_mag    = '0;
        s2n_exp_r  = '0;
        s2n_sign_r = 1'b0;
    end else begin
        // Zero-extend to give the adder/subtractor one extra bit for carry
        logic [SUM_W-1:0] Aext = {1'b0, s1_MA};
        logic [SUM_W-1:0] Bext = {1'b0, s1_MB_algn};

        // A >= B by construction in Stage 1
        s2n_mag = s1_add_op ? (Aext + Bext) : (Aext - Bext);

        // Carry forward exponent/sign of larger-magnitude operand
        s2n_exp_r  = s1_eA;
        s2n_sign_r = s1_signA;
    end
end

//  Register Stage 2 Outputs
always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
        s2_v          <= 1'b0;
        s2_mag        <= '0;
        s2_exp_r      <= '0;
        s2_sign_r     <= 1'b0;
        s2_special    <= 1'b0;
        s2_special_res<= '0;
    end else begin
        s2_v           <= s1_v;           // pass the valid signal through
        s2_mag         <= s2n_mag;
        s2_exp_r       <= s2n_exp_r;
        s2_sign_r      <= s2n_sign_r;
        s2_special     <= s2n_special;
        s2_special_res <= s2n_special_res;
    end
end

// Stage 3: Normalize, Round, and Pack

logic [15:0] s3n_out; 
logic        s3n_ovf;

always_comb begin
    s3n_out = '0;
    s3n_ovf = 1'b0;

    if (s2_special || !s2_v) begin
        s3n_out = s2_special ? s2_special_res : 16'd0;
    end else if (s2_mag == '0) begin
        s3n_out = {1'b0, 5'd0, 10'd0};
    end else begin
        // Normalization
        logic [SUM_W-1:0] mag   = s2_mag;
        logic [EXP_W-1:0] exp_r = s2_exp_r;
        logic [SUM_W-1:0] norm;
        logic [EXP_W-1:0] exp_n;

        logic carry = mag[SUM_W-1];`
        if (carry) begin
            // Right shift 1, OR the dropped LSB into sticky
            logic tail = mag[0];
            norm  = mag >> 1;
            norm[0] = norm[0] | tail;
            exp_n = exp_r + 1;
        end else begin
            // Left/right normalize using LZC and a single shift
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

        logic [SIG_W-1:0] sig11 = norm[GRS_W +: SIG_W];
        logic guard = norm[2];
        logic round = norm[1];
        logic sticky= norm[0];

        logic carry_up;
        logic [SIG_W-1:0] sig_rnd = round_rne(sig11, guard, round, sticky, carry_up);

        logic [EXP_W-1:0] exp_post = exp_n + (carry_up ? 1 : 0);
        logic [SIG_W-1:0] sig_post = carry_up ? {1'b1, {FRAC_W{1'b0}}} : sig_rnd;

        if (exp_post >= 5'h1F) begin
        // Overflow = ±Inf
            s3n_out = {s2_sign_r, 5'h1F, 10'h000};
            s3n_ovf = 1'b1;
        end else if (exp_post == 0) begin
        // Subnormal or zero: drop hidden bit
            logic [FRAC_W-1:0] subf = sig_post[FRAC_W-1:0];
            s3n_out = (subf == 0) ? {1'b0, 5'd0, 10'd0} : {s2_sign_r, 5'd0, subf};
            s3n_ovf = 1'b0;
        end else begin
        // Normalization
            s3n_out = {s2_sign_r, exp_post, sig_post[FRAC_W-1:0]};
            s3n_ovf = 1'b0;
        end
    end
end

// Register Stage 3 Outputs
always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
        s3_v   <= 1'b0;
        s3_out <= '0;
        s3_ovf <= 1'b0;
    end else begin
        s3_v   <= s2_v;        // valid propagates forward
        s3_out <= s3n_out;
        s3_ovf <= s3n_ovf;
    end
end

// Final Outputs
assign vaddsubif.out      = s3_v ? s3_out : 16'b0;
assign vaddsubif.overflow = s3_v ? s3_ovf : 1'b0;


endmodule