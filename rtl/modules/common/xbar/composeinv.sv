module composeinv #(
    parameter int SIZE=32,
    parameter int TAGWIDTH=5
)(
    input logic     [TAGWIDTH-1:0] pi   [SIZE-1:0],
    input logic     [TAGWIDTH-1:0] c    [SIZE-1:0],
    output logic    [TAGWIDTH-1:0] out  [SIZE-1:0]
);
    always_comb begin : inverse
        for (int i = 0; i < SIZE; i++) begin
            out[c[i]] = pi[i];
        end
    end
endmodule