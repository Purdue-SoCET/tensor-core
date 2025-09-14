`default_nettype none
module fa (
  input logic a, b, cin,
  output logic S, cout
);
  assign S = a ^ b ^ cin;
  assign cout = (a & b) | (cin & (a ^ b));
endmodule