`include "fust_s_if.vh"
`include "datapath_types.vh"

module fust_s (
    input logic CLK, nRST,
    fust_s_if.FUSTS fuif
);

  import datapath_pkg::*;

  fust_s_t fust;
  
  always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST)
      fuif.fust <= '0;
    else
      fuif.fust <= fust;
  end

  always_comb begin
    fust = fuif.fust;
    fust.op[fuif.fu] = fuif.en ? fuif.fust_row : fuif.fust.op[fuif.fu];
    fust.busy = fuif.busy;
    fust.t1 = fuif.t1;
    fust.t2 = fuif.t2;

    for (int i = 0; i < 3; i++) begin
      if (fuif.flush) begin
        fust.op = '0;
        fust.t1 = '0;
        fust.t2 = '0;
      end
    end

  end

endmodule
