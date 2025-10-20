module compare_switch #(
    parameter int DATA_W = 16,
    parameter int TAG_W  = 5
) (
    input logic [DATA_W-1:0] din [2],
    input logic [TAG_W-1:0]  tin [2],
    input logic cntrl,
    output logic [DATA_W-1:0] dout [2],
    output logic [TAG_W-1:0] tout [2]
);
    crossover_switch #(.SIZE(DATA_W)) u_xdat (.din(din), .cntrl(cntrl), .dout(dout));
    crossover_switch #(.SIZE(TAG_W))  u_xtag (.din(tin), .cntrl(cntrl), .dout(tout));
endmodule
