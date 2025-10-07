// 1 bit half adder
// used in wallace tree multiplier
// by Mixuan Pan, Sept 2025


module ha (
    input logic a, b, 
    output logic s, cout
);
    assign s = a ^ b; 
    assign cout = a & b; 
endmodule
