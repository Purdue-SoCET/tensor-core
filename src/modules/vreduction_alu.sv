`include "vector_types.vh"
`include "vaddsub_if.vh"
`include "vreduction_alu_if.vh"


module vreduction_alu (
    input logic CLK,
    input logic nRST,
    vreduction_alu_if.vralu vraluif
);

import vector_pkg::*;


vaddsub_if as_if ();
vaddsub adder (CLK, nRST, as_if);

// NaN detection logic
logic a_is_nan, b_is_nan, any_nan;

always_comb begin
    // Check if value_a is NaN (exponent all 1s, mantissa non-zero)
    a_is_nan = (&vraluif.value_a[14:10]) && (|vraluif.value_a[9:0]);
    
    // Check if value_b is NaN (exponent all 1s, mantissa non-zero)
    b_is_nan = (&vraluif.value_b[14:10]) && (|vraluif.value_b[9:0]);
    
    // Set flag if any input is NaN
    any_nan = a_is_nan | b_is_nan;
end

//interface connections
always_comb begin
    as_if.port_a = vraluif.value_a;
    as_if.port_b = vraluif.value_b;
    as_if.enable = 'b1;
end

//output logic
always_comb begin
    if (any_nan) begin
        // If any input is NaN, output NaN (canonical NaN: sign=0, exp=all 1s, mantissa=0x200)
        vraluif.value_out = 16'h7E00;
    end
    else if (vraluif.alu_op == VR_SUM) begin
        vraluif.value_out = as_if.out;
    end
    else if (vraluif.alu_op == VR_MIN) begin
        if (as_if.out[15]) begin
            vraluif.value_out = vraluif.value_a;
        end
        else begin
            vraluif.value_out = vraluif.value_b;
        end
    end
    else if (vraluif.alu_op == VR_MAX) begin
        if (as_if.out[15]) begin
            vraluif.value_out = vraluif.value_b;
        end
        else begin
            vraluif.value_out = vraluif.value_a;
        end
    end
end

//operation logic
always_comb begin
    if (vraluif.alu_op == VR_SUM) begin
        as_if.sub = 'b0;
    end
    else begin
        as_if.sub = 'b1;
    end
end

endmodule