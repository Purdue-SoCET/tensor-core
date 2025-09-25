`default_nettype none
// error - 0: output is +/-0, 1: output is +/-infinite, 2: output is NaN, 3: output is valid 
// wtm for 16 bits -> 
module wtm_fp16 (
    input logic [15:0] A, B, 
    output logic [15:0] S, 
    output logic [1:0] E // error 
); 
    // sign bit 0 -> +, 1 -> - 
    assign S[15] = A[15] ^ B[15]; 

    // exponent summation 
    assign S[14:10] = A[14:10] + B[14:10]; 

    // error message 
    assign E = (A[14:0] == 15'h0000 || B[14:0] == 15'h0000) ? 2'd0 :      // zero
           ((A[14:10] == 5'b11111 && A[9:0] == 10'd0) || 
            (B[14:10] == 5'b11111 && B[9:0] == 10'd0)) ? 2'd1 :       // infinity
           ((A[14:10] == 5'b11111 && A[9:0] != 10'd0) || 
            (B[14:10] == 5'b11111 && B[9:0] != 10'd0)) ? 2'd2 :       // NaN
           2'd3;  // valid 

  logic [86:0] s; 
  logic [104:0] c; 
  
// decimal wallace tree multiplication 

  // First Stage 
  ha ha01 (.a(A[0] && B[1]), .b(A[1] && B[0]), .s(), .cout(c[0]));
  fa fa02 (.a(A[0] && B[2]), .b(A[1] && B[1]), .cin(A[2] && B[0]), .s(s[0]), .cout(c[1]));
  fa fa03 (.a(A[0] && B[3]), .b(A[1] && B[2]), .cin(A[2] && B[1]), .s(s[1]), .cout(c[2]));
  fa fa04 (.a(A[0] && B[4]), .b(A[1] && B[3]), .cin(A[2] && B[2]), .s(s[2]), .cout(c[3]));
  fa fa05 (.a(A[0] && B[5]), .b(A[1] && B[4]), .cin(A[2] && B[3]), .s(s[3]), .cout(c[4]));
  fa fa06 (.a(A[0] && B[6]), .b(A[1] && B[5]), .cin(A[2] && B[4]), .s(s[4]), .cout(c[5]));
  fa fa07 (.a(A[0] && B[7]), .b(A[1] && B[6]), .cin(A[2] && B[5]), .s(s[5]), .cout(c[6]));
  fa fa08 (.a(A[0] && B[8]), .b(A[1] && B[7]), .cin(A[2] && B[6]), .s(s[6]), .cout(c[7]));
  fa fa09 (.a(A[0] && B[9]), .b(A[1] && B[8]), .cin(A[2] && B[7]), .s(s[7]), .cout(c[8]));
  ha ha010 (.a(A[1] && B[9]), .b(A[2] && B[8]), .s(s[8]), .cout(c[9]));
  ha ha011 (.a(A[3] && B[1]), .b(A[4] && B[0]), .s(s[9]), .cout(c[10]));
  fa fa012 (.a(A[3] && B[2]), .b(A[4] && B[1]), .cin(A[5] && B[0]), .s(s[10]), .cout(c[11]));
  fa fa013 (.a(A[3] && B[3]), .b(A[4] && B[2]), .cin(A[5] && B[1]), .s(s[11]), .cout(c[12]));
  fa fa014 (.a(A[3] && B[4]), .b(A[4] && B[3]), .cin(A[5] && B[2]), .s(s[12]), .cout(c[13]));
  fa fa015 (.a(A[3] && B[5]), .b(A[4] && B[4]), .cin(A[5] && B[3]), .s(s[13]), .cout(c[14]));
  fa fa016 (.a(A[3] && B[6]), .b(A[4] && B[5]), .cin(A[5] && B[4]), .s(s[14]), .cout(c[15]));
  fa fa017 (.a(A[3] && B[7]), .b(A[4] && B[6]), .cin(A[5] && B[5]), .s(s[15]), .cout(c[16]));
  fa fa018 (.a(A[3] && B[8]), .b(A[4] && B[7]), .cin(A[5] && B[6]), .s(s[16]), .cout(c[17]));
  fa fa019 (.a(A[3] && B[9]), .b(A[4] && B[8]), .cin(A[5] && B[7]), .s(s[17]), .cout(c[18]));
  ha fa020 (.a(A[4] && B[9]), .b(A[5] && B[8]), .s(s[18]), .cout(c[19]));
  ha ha021 (.a(A[6] && B[1]), .b(A[7] && B[0]), .s(s[19]), .cout(c[20]));
  fa fa022 (.a(A[6] && B[2]), .b(A[7] && B[1]), .cin(A[8] && B[0]), .s(s[20]), .cout(c[21]));
  fa fa023 (.a(A[6] && B[3]), .b(A[7] && B[2]), .cin(A[8] && B[1]), .s(s[21]), .cout(c[22]));
  fa fa024 (.a(A[6] && B[4]), .b(A[7] && B[3]), .cin(A[8] && B[2]), .s(s[22]), .cout(c[23]));
  fa fa025 (.a(A[6] && B[5]), .b(A[7] && B[4]), .cin(A[8] && B[3]), .s(s[23]), .cout(c[24]));
  fa fa026 (.a(A[6] && B[6]), .b(A[7] && B[5]), .cin(A[8] && B[4]), .s(s[24]), .cout(c[25]));
  fa fa027 (.a(A[6] && B[7]), .b(A[7] && B[6]), .cin(A[8] && B[5]), .s(s[25]), .cout(c[26]));
  fa fa028 (.a(A[6] && B[8]), .b(A[7] && B[7]), .cin(A[8] && B[6]), .s(s[26]), .cout(c[27]));
  fa fa029 (.a(A[6] && B[9]), .b(A[7] && B[8]), .cin(A[8] && B[7]), .s(s[27]), .cout(c[28]));
  ha ha030 (.a(A[7] && B[9]), .b(A[8] && B[8]), .s(s[28]), .cout(c[29]));
  
  // Second Stage 
  ha ha11 (.a(c[0]), .b(s[0]), .s(), .cout(c[30]));
  fa fa12 (.a(c[1]), .b(s[1]), .cin(A[3] && B[0]), .s(s[29]), .cout(c[31]));
  fa fa13 (.a(c[2]), .b(s[2]), .cin(s[9]), .s(s[30]), .cout(c[32]));
  fa fa14 (.a(c[3]), .b(s[3]), .cin(c[10]), .s(s[31]), .cout(c[33]));
  fa fa15 (.a(c[4]), .b(s[4]), .cin(c[11]), .s(s[32]), .cout(c[34]));
  fa fa16 (.a(c[5]), .b(s[5]), .cin(c[12]), .s(s[33]), .cout(c[35]));
  fa fa17 (.a(c[6]), .b(s[6]), .cin(c[13]), .s(s[34]), .cout(c[36]));
  fa fa18 (.a(c[7]), .b(s[7]), .cin(c[14]), .s(s[35]), .cout(c[37]));
  fa fa19 (.a(c[8]), .b(s[8]), .cin(c[15]), .s(s[36]), .cout(c[38]));
  fa fa110 (.a(c[9]), .b(A[2] && B[9]), .cin(c[16]), .s(s[37]), .cout(c[39]));
  ha ha111 (.a(A[6] && B[0]), .b(s[11]), .s(s[38]), .cout(c[40])); 
  ha ha112 (.a(s[19]), .b(s[12]), .s(s[39]), .cout(c[41])); 
  fa fa113 (.a(s[13]), .b(c[20]), .cin(s[20]), .s(s[40]), .cout(c[42]));
  fa fa114 (.a(s[14]), .b(c[21]), .cin(s[21]), .s(s[41]), .cout(c[43]));
  fa fa115 (.a(s[15]), .b(c[22]), .cin(s[22]), .s(s[42]), .cout(c[44]));
  fa fa116 (.a(s[16]), .b(c[23]), .cin(s[23]), .s(s[43]), .cout(c[45]));
  fa fa117 (.a(s[17]), .b(c[24]), .cin(s[24]), .s(s[44]), .cout(c[46]));
  fa fa118 (.a(s[18]), .b(c[25]), .cin(s[25]), .s(s[45]), .cout(c[47]));
  fa fa119 (.a(A[5] && B[9]), .b(c[26]), .cin(s[26]), .s(s[46]), .cout(c[48]));
  ha ha120 (.a(c[27]), .b(s[27]), .s(s[47]), .cout(c[49]));
  ha ha121 (.a(c[28]), .b(s[28]), .s(s[48]), .cout(c[50]));
  ha ha122 (.a(c[29]), .b(A[8] && B[9]), .s(s[49]), .cout(c[51]));
  
  // Third Stage 
  ha ha21 (.a(c[30]), .b(s[29]), .s(), .cout(c[52]));
  ha ha22 (.a(c[31]), .b(s[30]), .s(s[50]), .cout(c[53]));
  fa fa23 (.a(c[32]), .b(s[31]), .cin(s[10]), .s(s[51]), .cout(c[54]));
  fa fa24 (.a(c[33]), .b(s[32]), .cin(s[38]), .s(s[52]), .cout(c[55]));
  fa fa25 (.a(c[34]), .b(s[33]), .cin(c[40]), .s(s[53]), .cout(c[56]));
  fa fa26 (.a(c[35]), .b(s[34]), .cin(c[41]), .s(s[54]), .cout(c[57]));
  fa fa27 (.a(c[36]), .b(s[35]), .cin(c[42]), .s(s[55]), .cout(c[58]));
  fa fa28 (.a(c[37]), .b(s[36]), .cin(c[43]), .s(s[56]), .cout(c[59]));
  fa fa29 (.a(c[38]), .b(s[37]), .cin(c[44]), .s(s[57]), .cout(c[60]));
  fa fa210 (.a(c[39]), .b(c[17]), .cin(c[45]), .s(s[58]), .cout(c[61]));
  ha ha211 (.a(c[40]), .b(c[46]), .s(s[59]), .cout(c[62]));
  ha ha212 (.a(c[41]), .b(c[47]), .s(s[60]), .cout(c[63]));
  
  // Fourth Stage 
  ha ha31 (.a(c[52]), .b(s[50]), .s(), .cout(c[64]));
  ha ha32 (.a(c[53]), .b(s[51]), .s(s[61]), .cout(c[65]));
  ha ha33 (.a(c[54]), .b(s[52]), .s(s[62]), .cout(c[66]));
  fa fa34 (.a(c[55]), .b(s[53]), .cin(s[39]), .s(s[63]), .cout(c[67]));
  fa fa35 (.a(c[56]), .b(s[54]), .cin(s[40]), .s(s[64]), .cout(c[68]));
  fa fa36 (.a(c[57]), .b(s[55]), .cin(s[41]), .s(s[65]), .cout(c[69]));
  fa fa37 (.a(c[58]), .b(s[56]), .cin(s[42]), .s(s[66]), .cout(c[70]));
  fa fa38 (.a(c[59]), .b(s[57]), .cin(s[43]), .s(s[67]), .cout(c[71]));
  fa fa39 (.a(c[60]), .b(s[58]), .cin(s[44]), .s(s[68]), .cout(c[72]));
  fa fa310 (.a(c[61]), .b(s[59]), .cin(s[45]), .s(s[69]), .cout(c[73]));
  fa fa311 (.a(c[62]), .b(s[60]), .cin(s[46]), .s(s[70]), .cout(c[74]));
  fa fa312 (.a(c[63]), .b(c[48]), .cin(s[47]), .s(s[71]), .cout(c[75]));
  ha ha313 (.a(s[62]), .b(s[48]), .s(s[72]), .cout(c[76]));
  ha ha314 (.a(s[63]), .b(s[49]), .s(s[73]), .cout(c[77]));

  // Fifth Stage 
  ha ha41 (.a(c[64]), .b(s[61]), .s(), .cout(c[78]));
  ha ha42 (.a(c[65]), .b(s[62]), .s(s[74]), .cout(c[79]));
  ha ha43 (.a(c[66]), .b(s[63]), .s(s[75]), .cout(c[80]));
  ha ha44 (.a(c[67]), .b(s[64]), .s(s[76]), .cout(c[81]));
  fa fa45 (.a(c[68]), .b(s[65]), .cin(A[9] && B[0]), .s(s[77]), .cout(c[82]));
  fa fa46 (.a(c[69]), .b(s[66]), .cin(A[9] && B[1]), .s(s[78]), .cout(c[83]));
  fa fa47 (.a(c[70]), .b(s[67]), .cin(A[9] && B[2]), .s(s[79]), .cout(c[84]));
  fa fa48 (.a(c[71]), .b(s[68]), .cin(A[9] && B[3]), .s(s[80]), .cout(c[85]));
  fa fa49 (.a(c[72]), .b(s[69]), .cin(A[9] && B[4]), .s(s[81]), .cout(c[86]));
  fa fa410 (.a(c[73]), .b(s[70]), .cin(A[9] && B[5]), .s(s[82]), .cout(c[87]));
  fa fa411 (.a(c[74]), .b(s[71]), .cin(A[9] && B[6]), .s(s[83]), .cout(c[88]));
  fa fa412 (.a(c[75]), .b(s[72]), .cin(A[9] && B[7]), .s(s[84]), .cout(c[89]));
  fa fa413 (.a(c[76]), .b(s[73]), .cin(A[9] && B[8]), .s(s[85]), .cout(c[90]));
  fa fa414 (.a(c[77]), .b(c[51]), .cin(A[9] && B[9]), .s(s[86]), .cout(c[91]));

  // Sixth Stage (Vector Merge)
  ha ha51 (.a(c[78]), .b(s[74]), .s(), .cout(c[92])); 
  fa fa52 (.a(c[79]), .b(s[75]), .cin(c[92]), .s(), .cout(c[93])); 
  fa fa53 (.a(c[80]), .b(s[76]), .cin(c[93]), .s(), .cout(c[94]));
  fa fa54 (.a(c[81]), .b(s[77]), .cin(c[94]), .s(), .cout(c[95]));
  fa fa55 (.a(c[82]), .b(s[78]), .cin(c[95]), .s(), .cout(c[96]));
  fa fa56 (.a(c[83]), .b(s[79]), .cin(c[96]), .s(S[0]), .cout(c[97]));
  fa fa57 (.a(c[84]), .b(s[80]), .cin(c[97]), .s(S[1]), .cout(c[98]));
  fa fa58 (.a(c[85]), .b(s[81]), .cin(c[98]), .s(S[2]), .cout(c[99]));
  fa fa59 (.a(c[86]), .b(s[82]), .cin(c[99]), .s(S[3]), .cout(c[100]));
  fa fa510 (.a(c[87]), .b(s[83]), .cin(c[100]), .s(S[4]), .cout(c[101]));
  fa fa511 (.a(c[88]), .b(s[84]), .cin(c[101]), .s(S[5]), .cout(c[102]));
  fa fa512 (.a(c[89]), .b(s[85]), .cin(c[102]), .s(S[6]), .cout(c[103]));
  fa fa513 (.a(c[90]), .b(s[86]), .cin(c[103]), .s(S[7]), .cout(c[104]));
  ha fa514 (.a(c[91]), .b(c[104]), .s(S[8]), .cout(S[9]));
  
endmodule