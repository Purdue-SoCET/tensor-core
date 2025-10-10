`default_nettype none
// error - 0: output is +/-0, 1: output is +/-infinite, 2: output is NaN, 3: output is valid 
// wtm for 16 bits -> 
module wtm_bf16 (
    input logic [15:0] A, B, 
    output logic [15:0] S, 
    output logic [1:0] E // error 
); 
    // sign bit 0 -> +, 1 -> - 
    assign S[15] = A[15] ^ B[15]; 

    // error message 
    assign E = A[14:0] == 0 || B[14:0] == 0 ? 0 : 
      {1'b0, A[14:0]} == 16'h7f80 || {1'b0, B[14:0]} == 16'h7f80 ? 1 : 
      (A[14:7] == '1 && A[6:0] != 0) || (B[14:7] == '1 && B[6:0] != 0) ? 'd2 : 'd3; 
    
    logic [31:0] Z; // 32-bit wtm output product 
    
    logic [74:0] S0, C0; 
    logic [46:0] S1, C1; 
    logic [34:0] S2, C2; 


    // First Stage 
    assign Z[0] = A[0] && B[0]; 

    // Second Stage 

    // Third Stage (Vector Merge)

    // Decimal Placement & Z -> S
endmodule