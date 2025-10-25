`include "vector_types.vh"
`include "vector_if.vh"
`include "vexp_if.vh"

module vexp (
    input logic CLK,
    input logic nRST,
    vexp_if.vexp vexpif
);

import vector_pkg::*;

vaddsub_if vaddsubif1(); //vector add/sub instantiation 1
vaddsub_if vaddsubif2(); //vector add/sub instatiation 2
vaddsub_if vaddsubif3(); //vector add/sub instatiation 3


vaddsub VADDSUB1 ( //connecting the module's appropriate signals
    .CLK(CLK),
    .nRST(nRST),
    .vaddsub(vaddsubif1)
);

vaddsub VADDSUB2 (
    .CLK(CLK),
    .nRST(nRST),
    .vaddsub(vaddsubif2)
);

vaddsub VADDSUB3 (
    .CLK(CLK),
    .nRST(nRST),
    .vaddsub(vaddsubif3)
);

mul_fp16 MUL1 (
    .CLK(CLK),
    .nRST(nRST)
);

mul_fp16 MUL2 (
    .CLK(CLK),
    .nRST(nRST)
);
mul_fp16 MUL3 (
    .CLK(CLK),
    .nRST(nRST)
);

logic [15:0]
            add1_in, add1_out, add1_result, mul1_in, mul1_out, mul1_result, //stage 1
            add2_in, add2_out, mul2_in, mul2_out, mul2_result,              //stage 2
            mul3_result,                                                    //stage 3
            add4_in, add4_out;                                              //final stage

fp16_t fp1; //declaring the fp16 type
logic [15:0] onesixth, one, t_series_approx, poweroftwo;

assign fp1 = vexpif.port_a;
assign onesixth = 16'b0011000101010101; //1/6 in fp16 format
assign one = 16'b0011110000000000;

// STAGE 1: Add (1 + r) & Multiply (r * r)

//Addition
assign vaddsubif1.port_a = one;
assign vaddsubif1.port_b = {fp1.sign, 5'b0, fp1.frac}; //adding the sign bit to the mantissa
assign add1_result = vaddsubif1.out;
assign add1_in = add1_result;

//Mulitplication
assign fp16mulif1.port_a = {fp1.sign, 5'b0, fp1.frac};
assign fp16mulif1.port_b = {fp1.sign, 5'b0, fp1.frac};
assign mul1_result = fp16mulif1.out;
assign mul1_in = mul1_result;


always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
        add1_out <= '0;
        mul1_out <= '0;
    end
    else begin
        add1_out <= add1_in;
        mul1_out <= mul1_in;
    end
end

// STAGE 2: Add(1 + r + r^2/2) & Multiply (r^2 * r)

//Shift the r^2 term by 2
assign mul2_result = {mul1_out[15], (mul1_out[14:10] + 1), mul1_out[9:0] >> 1}; //shifting the mantissa right by 1 and incrementing the exponent by 1

//Addition
assign vaddsubif2.port_a = mul2_result;;
assign vaddsubif2.port_b = add1_out;
assign add2_in = vaddsubif2.out;

//Multiplication
assign fp16mulif2.port_a = mul1_out;
assign fp16mulif2.port_b = {fp1.sign, 5'b0, fp1.frac};
assign mul2_in = fp16mulif2.out;

always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
        add2_out <= 0;
        mul2_out <= 0;
    end
    else begin
        add2_out <= add2_in;
        mul2_out <= mul2_in;
    end
end

// STAGE 3: Add(1 + r + r^2/2 + r^3/6) & (Multiply r^3 * 1/6)

//Multiplied by 1/6
assign fp16mulif3.port_a = mul2_out;
assign fp16mulif3.port_b = onesixth;
assign mul3_result = fp16mulif3.out;

//Addition
assign vaddsubif3.port_a = mul3_result;
assign vaddsubif3.port_b = add2_out;
assign t_series_approx = vaddsubif3.out;
assign add4_in = t_series_approx;

always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
        add4_out <= '0;
    end
    else begin
        add4_out <= add4_in;
    end
end

// STAGE 4: Multiply (Taylor Series Approximation * 2^q)

//Shifted Value
assign poweroftwo = {1'b1, (fp1.exp), 10'b0}; // 2^q value from exponent field

assign fp16mulif4.port_a = add4_out;
assign fp16mulif4.port_b = poweroftwo;
assign vexpif.out = fp16mulif4.out;

endmodule