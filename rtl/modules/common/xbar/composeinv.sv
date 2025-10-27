module composeinv #(
    parameter int SIZE=32,
    parameter int TAGWIDTH=5
)(
    input logic     [TAGWIDTH-1:0] c    [SIZE],
    input logic     [TAGWIDTH-1:0] pi   [SIZE],
    output logic    [TAGWIDTH-1:0] out  [SIZE],
);
    always_comb begin : inverse
        for (int i = 0; i < SIZE; i++) begin
            out[pi[i]] = c[i];
        end
    end
endmodule