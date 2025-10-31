// 1 bit half adder
// used in wallace tree multiplier
// by Mixuan Pan, Sept 2025

`timescale 1ns/1ps

// `default_nettype none

module ha (
    input logic a, b, 
    output logic s, cout
);
    assign s = a ^ b; 
    assign cout = a & b; 
endmodule