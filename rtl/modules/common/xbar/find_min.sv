module find_min #(
    parameter int SIZE=32,
    parameter int TAGWIDTH=5
) (
    input logic  [TAGWIDTH-1:0] in [2][SIZE-1:0],
    output logic [TAGWIDTH-1:0] out [SIZE-1:0]
);
    always_comb begin : findmin
        for (int i = 0; i < SIZE; i++) begin
            out[i] = in[0][i] < in[1][i] ? in[0][i] : in[1][i];
        end
    end

endmodule