`include "vector_types.vh"
`include "vector_if.vh"
`include "vexp_if.vh"
`include "vaddsub_if.vh"   // includes the vaddsub interface

module vexp (
    input  logic       CLK,
    input  logic       nRST,
    vexp_if.vexp       vexpif
);

    import vector_pkg::*;
    
    //instantiating the adders
    vaddsub_if vaddsubif1(); 
    vaddsub_if vaddsubif2();
    vaddsub_if vaddsubif3();

    vaddsub VADDSUB1 (.CLK(CLK), .nRST(nRST), .vaddsubif(vaddsubif1));
    vaddsub VADDSUB2 (.CLK(CLK), .nRST(nRST), .vaddsubif(vaddsubif2));
    vaddsub VADDSUB3 (.CLK(CLK), .nRST(nRST), .vaddsubif(vaddsubif3));


    // S1
    logic        mul1_start, mul1_done;
    logic [15:0] mul1_a, mul1_b, mul1_out;
    mul_fp16 MUL1 (.clk(CLK), .nRST(nRST), .start(mul1_start),
                   .a(mul1_a), .b(mul1_b), .result(mul1_out), .done(mul1_done));

    // S2
    logic        mul2_start, mul2_done;
    logic [15:0] mul2_a, mul2_b, mul2_out;
    mul_fp16 MUL2 (.clk(CLK), .nRST(nRST), .start(mul2_start),
                   .a(mul2_a), .b(mul2_b), .result(mul2_out), .done(mul2_done));

    // S3
    logic        mul3_start, mul3_done;
    logic [15:0] mul3_a, mul3_b, mul3_out;
    mul_fp16 MUL3 (.clk(CLK), .nRST(nRST), .start(mul3_start),
                   .a(mul3_a), .b(mul3_b), .result(mul3_out), .done(mul3_done));

    // S4 (final 2^q multiply)
    logic        mul4_start, mul4_done;
    logic [15:0] mul4_a, mul4_b, mul4_out;
    mul_fp16 MUL4 (.clk(CLK), .nRST(nRST), .start(mul4_start),
                   .a(mul4_a), .b(mul4_b), .result(mul4_out), .done(mul4_done));

    fp16_t fp1; assign fp1 = vexpif.port_a;

    localparam logic [15:0] ONE       = 16'h3C00;                  // +1.0
    localparam logic [15:0] ONE_SIXTH = 16'b0011000101010101;      // ~1/6

    logic [15:0] r_bits;
    // assign r_bits = {fp1.sign, 5'b0, fp1.frac};
    assign r_bits = vexpif.port_a;

    // ===========================================================================
    // Stage 1: (1 + r) and (r * r)
    // ===========================================================================
    // Adder (combinational)
    assign vaddsubif1.port_a = ONE;
    assign vaddsubif1.port_b = r_bits;
    assign vaddsubif1.enable = vexpif.enable;
    assign vaddsubif1.sub    = 1'b0;
    logic [15:0] s1_sum_comb;
    assign s1_sum_comb = vaddsubif1.out;   // (1 + r)

    // Mult: r * r
    assign mul1_a = r_bits;
    assign mul1_b = r_bits;

    // Start policy: accept a new op when enable = 1
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            mul1_start <= 1'b0;
        end
        else begin
            mul1_start <= vexpif.enable;
        end
    end

    // Capture both paths together on the done signal
    logic [15:0] s1_sum_q;   // (1 + r)
    logic [15:0] s1_r2_q;    // r^2
    logic        s1_v_q;     // valid pulse to Stage 2
    
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            s1_sum_q <= '0; 
            s1_r2_q <= '0; 
            s1_v_q <= 1'b0;
        end else if (mul1_done) begin
            s1_sum_q <= s1_sum_comb;
            s1_r2_q  <= mul1_out;
            s1_v_q   <= 1'b1;
        end else begin
            s1_v_q   <= 1'b0;
        end
    end

    // ===========================================================================
    // Stage 2: (1 + r + r^2/2) and (r^2 * r = r^3)
    // ===========================================================================
    // Quick fp16-ish r^2/2: shift mantissa >>1 and bump exponent +1 to make bit fields equivalent
    logic [15:0] r2_over_2;
    assign r2_over_2 = {s1_r2_q[15], (s1_r2_q[14:10] - 5'd1), s1_r2_q[9:0]};

    // Adder (combinational): s1_sum_q + r^2/2
    assign vaddsubif2.port_a = s1_sum_q;
    assign vaddsubif2.port_b = r2_over_2;
    assign vaddsubif2.enable = s1_v_q;
    assign vaddsubif2.sub    = 1'b0;
    logic [15:0] s2_sum_comb;
    assign s2_sum_comb = vaddsubif2.out;

    // Mult: r^2 * r = r^3
    assign mul2_a = s1_r2_q;
    assign mul2_b = r_bits;
    
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            mul2_start <= 1'b0;
        end else begin 
            mul2_start <= s1_v_q;
        end
    end

    logic [15:0] s2_sum_q, s2_r3_q;
    logic s2_v_q;
    
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            s2_sum_q <= '0; 
            s2_r3_q <= '0; 
            s2_v_q <= 1'b0;
        end else if (mul2_done) begin
            s2_sum_q <= s2_sum_comb;
            s2_r3_q  <= mul2_out;
            s2_v_q   <= 1'b1;
        end else begin
            s2_v_q <= 1'b0;
        end
    end

    // ===========================================================================
    // Stage 3: add r^3/6
    // ===========================================================================
    // Mult: r^3 * (1/6)
    assign mul3_a = s2_r3_q;
    assign mul3_b = ONE_SIXTH;
    
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            mul3_start <= 1'b0;
        end else begin
            mul3_start <= s2_v_q;
        end
    end

    // Add (1 + r + r^2/2) + (r^3/6). Capture on mul3_done.
    assign vaddsubif3.port_a = s2_sum_q;
    assign vaddsubif3.port_b = mul3_out;             // valid when mul3_done
    assign vaddsubif3.enable = mul3_done;
    assign vaddsubif3.sub    = 1'b0;

    logic [15:0] s3_sum_q; logic s3_v_q;
    
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            s3_sum_q <= '0; 
            s3_v_q <= 1'b0;
        end else if (mul3_done) begin
            s3_sum_q <= vaddsubif3.out;
            s3_v_q   <= 1'b1;
        end else begin
            s3_v_q   <= 1'b0;
        end
    end

    // ===========================================================================
    // Stage 4: multiply by 2^q (from exponent field)
    // ===========================================================================
    logic [15:0] poweroftwo;
    assign poweroftwo = ((fp1.exp == '0) && (fp1.frac == '0)) ? {fp1.sign, 5'b01111, 10'b0} : {fp1.sign, fp1.exp, 10'b0}; // quick 2^q encoding

    assign mul4_a = s3_sum_q;
    assign mul4_b = poweroftwo;
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin 
            mul4_start <= 1'b0;
        end else begin
            mul4_start <= s3_v_q;
        end
    end

    // Final output: update only on mul4_done
    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            vexpif.out <= '0;   
        end else if (mul4_done) begin
            vexpif.out <= mul4_out;
        end
    end

endmodule
