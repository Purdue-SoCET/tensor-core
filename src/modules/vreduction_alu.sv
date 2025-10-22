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

// Pipeline registers to match the 2-cycle adder latency
logic [15:0] value_a_s1, value_a_s2;
logic [15:0] value_b_s1, value_b_s2;
logic [1:0] alu_op_s1, alu_op_s2;
logic any_nan_s1, any_nan_s2;

//nan detection
logic a_is_nan, b_is_nan, any_nan;

always_comb begin
    a_is_nan = (&vraluif.value_a[14:10]) && (|vraluif.value_a[9:0]);
    b_is_nan = (&vraluif.value_b[14:10]) && (|vraluif.value_b[9:0]);
    any_nan = a_is_nan | b_is_nan;
end

// Stage 0: Adder/subtractor control
always_comb begin
    as_if.port_a = vraluif.value_a;
    as_if.port_b = vraluif.value_b;
    as_if.enable = 1'b1;
    
    // For MIN/MAX, we need to subtract to compare
    as_if.sub = (vraluif.alu_op == VR_MIN || vraluif.alu_op == VR_MAX);
end

// Pipeline Stage 1: Register inputs
always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
        value_a_s1 <= '0;
        value_b_s1 <= '0;
        alu_op_s1 <= 2'b00;
        any_nan_s1 <= '0;
    end else begin
        value_a_s1 <= vraluif.value_a;
        value_b_s1 <= vraluif.value_b;
        alu_op_s1 <= vraluif.alu_op;
        any_nan_s1 <= any_nan;
    end
end

// Pipeline Stage 2: Register again to align with adder output
always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
        value_a_s2 <= '0;
        value_b_s2 <= '0;
        alu_op_s2 <= 2'b00;
        any_nan_s2 <= '0;
    end else begin
        value_a_s2 <= value_a_s1;
        value_b_s2 <= value_b_s1;
        alu_op_s2 <= alu_op_s1;
        any_nan_s2 <= any_nan_s1;
    end
end


always_comb begin
    if (any_nan_s2) begin
        // If any input was NaN, output NaN
        vraluif.value_out = 16'h7D00;
    end
    else if (alu_op_s2 == VR_SUM) begin
        // For SUM, use the adder result directly
        vraluif.value_out = as_if.out;
    end
    else if (alu_op_s2 == VR_MIN) begin
        // For MIN: if (a-b) is negative, a is smaller
        if (as_if.out[15]) begin
            vraluif.value_out = value_a_s2;
        end else begin
            vraluif.value_out = value_b_s2;
        end
    end
    else if (alu_op_s2 == VR_MAX) begin
        // For MAX: if (a-b) is negative, b is larger
        if (as_if.out[15]) begin
            vraluif.value_out = value_b_s2;
        end else begin
            vraluif.value_out = value_a_s2;
        end
    end
    else begin
        vraluif.value_out = 16'h0000;
    end
end

endmodule