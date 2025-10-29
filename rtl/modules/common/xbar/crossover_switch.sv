module crossover_switch #(
    parameter int SIZE = 32
) (
    input var logic [SIZE-1:0] din  [2],
    input  logic            cntrl,
    output var logic [SIZE-1:0] dout [2]
);

    always_comb begin
        if (cntrl) begin
            dout[0] = din[1];
            dout[1] = din[0];
        end else begin
            dout[0] = din[0];
            dout[1] = din[1];
        end
    end
endmodule
