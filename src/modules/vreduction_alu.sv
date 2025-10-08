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

//interface connections
always_comb begin
    as_if.port_a = vraluif.value_a;
    as_if.port_b = vraluif.value_b;
    as_if.enable = 'b1;
end

//output logic
always_comb begin
    if (vraluif.alu_op == VR_SUM) begin
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