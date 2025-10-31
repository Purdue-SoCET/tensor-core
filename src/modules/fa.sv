// 1 bit full adder
// Used in wallace tree multiplier
// By: Mixuan Pan, Sep 2025

`timescale 1ns/1ps

// `default_nettype none

module fa (
  input logic a, b, cin,
  output logic s, cout
);
  assign s = a ^ b ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
  
endmodule