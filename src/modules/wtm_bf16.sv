`default_nettype none
// Wallace Tree Multiplier for BF16
module wtm_bf16 (
    input logic [15:0] A, B, 
    output logic [15:0] S, 
    output logic [1:0] E // error 
); 
    // sign bit 0 -> +, 1 -> - 
    assign S[15] = A[15] ^ B[15]; 

    // exponent summation (will need adjustment for bias later)
    logic [8:0] exp_sum;
    assign exp_sum = A[14:7] + B[14:7];
    
    // error message 
    assign E = (A[14:0] == 0 || B[14:0] == 0) ? 2'd0 : 
               (A[14:7] == 8'hFF) ? (A[6:0] == 0 ? 2'd1 : 2'd2) :
               (B[14:7] == 8'hFF) ? (B[6:0] == 0 ? 2'd1 : 2'd2) : 2'd3; 
    
    // assign implicit bits 
    logic A_imp, B_imp; 
    assign A_imp = A[14:7] != 8'h0; 
    assign B_imp = B[14:7] != 8'h0; 

    logic [60:0] s; 
    logic [71:0] c; 
    logic [11:0] temp; // temp final mantissa 
  
    // Stage 1 
    ha ha01 (.a(A[0] & B[1]), .b(A[1] & B[0]), .s(), .cout(c[0]));
    
    fa fa02 (.a(A[0] & B[2]), .b(A[1] & B[1]), .cin(A[2] & B[0]), .s(s[0]), .cout(c[1]));
    fa fa03 (.a(A[0] & B[3]), .b(A[1] & B[2]), .cin(A[2] & B[1]), .s(s[1]), .cout(c[2]));
    fa fa04 (.a(A[0] & B[4]), .b(A[1] & B[3]), .cin(A[2] & B[2]), .s(s[2]), .cout(c[3]));
    fa fa05 (.a(A[0] & B[5]), .b(A[1] & B[4]), .cin(A[2] & B[3]), .s(s[3]), .cout(c[4]));
    fa fa06 (.a(A[0] & B[6]), .b(A[1] & B[5]), .cin(A[2] & B[4]), .s(s[4]), .cout(c[5]));
    fa fa07 (.a(A[0] & B_imp), .b(A[1] & B[6]), .cin(A[2] & B[5]), .s(s[5]), .cout(c[6]));
    
    ha ha08 (.a(A[1] & B_imp), .b(A[2] & B[6]), .s(s[6]), .cout(c[7]));
    ha ha09 (.a(A[3] & B[1]), .b(A[4] & B[0]), .s(s[7]), .cout(c[8]));
    
    fa fa010 (.a(A[3] & B[2]), .b(A[4] & B[1]), .cin(A[5] & B[0]), .s(s[8]), .cout(c[9]));
    fa fa011 (.a(A[3] & B[3]), .b(A[4] & B[2]), .cin(A[5] & B[1]), .s(s[9]), .cout(c[10]));
    fa fa012 (.a(A[3] & B[4]), .b(A[4] & B[3]), .cin(A[5] & B[2]), .s(s[10]), .cout(c[11]));
    fa fa013 (.a(A[3] & B[5]), .b(A[4] & B[4]), .cin(A[5] & B[3]), .s(s[11]), .cout(c[12]));
    fa fa014 (.a(A[3] & B[6]), .b(A[4] & B[5]), .cin(A[5] & B[4]), .s(s[12]), .cout(c[13]));
    fa fa015 (.a(A[3] & B_imp), .b(A[4] & B[6]), .cin(A[5] & B[5]), .s(s[13]), .cout(c[14]));
    
    ha ha016 (.a(A[4] & B_imp), .b(A[5] & B[6]), .s(s[14]), .cout(c[15]));

    // Stage 2
    ha ha11 (.a(c[0]), .b(s[0]), .s(s[15]), .cout(c[16]));
    fa fa12 (.a(c[1]), .b(s[1]), .cin(A[3] & B[0]), .s(s[16]), .cout(c[17]));
    fa fa13 (.a(c[2]), .b(s[2]), .cin(s[7]), .s(s[17]), .cout(c[18]));
    fa fa14 (.a(c[3]), .b(s[3]), .cin(c[8]), .s(s[18]), .cout(c[19]));
    fa fa15 (.a(c[4]), .b(s[4]), .cin(c[9]),      .s(s[19]), .cout(c[20]));
    fa fa16 (.a(c[5]), .b(s[5]), .cin(c[10]),     .s(s[20]), .cout(c[21]));
    fa fa17 (.a(c[6]), .b(s[6]), .cin(c[11]),     .s(s[21]), .cout(c[22]));
    fa fa18 (.a(c[7]), .b(A[2] & B_imp), .cin(c[12]),.s(s[22]), .cout(c[23]));
    fa fa19 (.a(c[13]), .b(s[8]), .cin(c[14]),    .s(s[23]), .cout(c[24]));
    ha ha110 (.a(c[15]), .b(s[9]),               .s(s[24]), .cout(c[25]));
    fa fa111 (.a(A[6] & B[2]), .b(s[11]), .cin(A_imp & B[1]), .s(s[25]), .cout(c[26]));
    fa fa112 (.a(A[6] & B[3]), .b(s[12]), .cin(A_imp & B[2]), .s(s[26]), .cout(c[27]));
    fa fa113 (.a(A[6] & B[4]), .b(s[13]), .cin(A_imp & B[3]), .s(s[27]), .cout(c[28]));
    fa fa114 (.a(A[6] & B[5]), .b(s[14]), .cin(A_imp & B[4]), .s(s[28]), .cout(c[29]));
    fa fa115 (.a(A[6] & B[6]), .b(A[5] & B_imp), .cin(A_imp & B[5]), .s(s[29]), .cout(c[30]));
    ha ha116 (.a(A[6] & B_imp), .b(A_imp & B[6]), .s(s[30]), .cout(c[31]));

    // Stage 3
    ha ha21 (.a(c[16]), .b(s[16]), .s(s[31]), .cout(c[32]));
    ha ha22 (.a(c[17]), .b(s[17]), .s(s[32]), .cout(c[33]));
    fa fa23 (.a(c[18]), .b(s[18]), .cin(s[8]), .s(s[33]), .cout(c[34]));
    fa fa24 (.a(c[19]), .b(s[19]), .cin(s[23]), .s(s[34]), .cout(c[35]));
    fa fa25 (.a(c[20]), .b(s[20]), .cin(c[24]), .s(s[35]), .cout(c[36]));
    fa fa26   (.a(c[21]), .b(s[21]), .cin(c[25]),  .s(s[36]), .cout(c[37]));
    fa fa27   (.a(c[22]), .b(s[22]), .cin(c[26]),  .s(s[37]), .cout(c[38]));
    fa fa28   (.a(c[23]), .b(c[13]), .cin(c[27]),  .s(s[38]), .cout(c[39]));
    ha ha29 (.a(c[14]), .b(c[28]), .s(s[39]), .cout(c[40])); 
    ha ha210 (.a(c[15]), .b(c[29]), .s(s[40]), .cout(c[41])); 
   
    // Stage 4
    ha ha31 (.a(c[32]), .b(s[32]), .s(temp[0]), .cout(c[42]));
    ha ha32 (.a(c[33]), .b(s[33]), .s(s[41]), .cout(c[43]));
    ha ha33 (.a(c[34]), .b(s[34]), .s(s[42]), .cout(c[44]));
    fa fa34 (.a(c[35]), .b(s[35]), .cin(s[24]),   .s(s[43]), .cout(c[45]));
    fa fa35 (.a(c[36]), .b(s[36]), .cin(s[25]),   .s(s[44]), .cout(c[46]));
    fa fa36 (.a(c[37]), .b(s[37]), .cin(s[26]),   .s(s[45]), .cout(c[47]));
    fa fa37 (.a(c[38]), .b(s[38]), .cin(s[27]),   .s(s[46]), .cout(c[48]));
    fa fa38 (.a(c[39]), .b(s[39]), .cin(s[28]),   .s(s[47]), .cout(c[49]));
    fa fa39 (.a(c[40]), .b(s[40]), .cin(s[29]),   .s(s[48]), .cout(c[50]));
    fa fa310 (.a(c[41]), .b(c[30]), .cin(s[30]),   .s(s[49]), .cout(c[51]));
    ha ha311 (.a(c[31]), .b(A_imp & B_imp), .s(s[50]), .cout(c[52]));

    // Final Stage - Ripple Carry Adder
    ha ha41 (.a(c[42]), .b(s[41]), .s(temp[1]), .cout(c[51]));
    
    fa fa42 (.a(c[43]), .b(s[42]), .cin(c[51]), .s(temp[2]), .cout(c[52]));
    fa fa43 (.a(c[44]), .b(s[43]), .cin(c[52]), .s(temp[3]),  .cout(c[53]));
    fa fa44 (.a(c[45]), .b(s[44]), .cin(c[53]), .s(temp[4]),  .cout(c[54]));
    fa fa45 (.a(c[46]), .b(s[45]), .cin(c[54]), .s(temp[5]),  .cout(c[55]));
    fa fa46 (.a(c[47]), .b(s[46]), .cin(c[55]), .s(temp[6]),  .cout(c[56]));
    fa fa47 (.a(c[48]), .b(s[47]), .cin(c[56]), .s(temp[7]),  .cout(c[57]));
    fa fa48 (.a(c[49]), .b(s[48]), .cin(c[57]), .s(temp[8]),  .cout(c[58]));
    fa fa49 (.a(c[50]), .b(s[49]), .cin(c[58]), .s(temp[9]),  .cout(c[59]));
    fa fa50 (.a(c[51]), .b(s[50]), .cin(c[59]), .s(temp[10]), .cout(c[60]));
    ha ha51 (.a(c[52]), .b(c[60]), .s(temp[11]), .cout());

    // Normalization and Rounding Logic
    logic [6:0] mantissa_prenorm;
    logic [2:0] round_bits; // Guard, Round, Sticky
 
    // Select mantissa bits based on normalization
    assign mantissa_prenorm = temp[11] ? temp[10:4] : temp[9:3];
    
    // Extract rounding bits
    assign round_bits = temp[11] ? temp[3:1] : temp[2:0]; // Guard, Round, Sticky (i'm only using 1 bit for sticky )
    
    // Round to nearest, ties to even
    logic round_up;
    assign round_up = round_bits[2] & (round_bits[1] | round_bits[0] | mantissa_prenorm[0]);
    
    logic [7:0] mantissa_rounded;
    assign mantissa_rounded = mantissa_prenorm + round_up;
    
    // Final exponent calculation
    assign S[14:7] = exp_sum - 8'd127 + temp[11] + mantissa_rounded[7]; // overflow 
    
    // Final mantissa (only 7 explicit bits)
    assign S[6:0] = mantissa_rounded[7] ? 7'b0 : mantissa_rounded[6:0];
    
endmodule