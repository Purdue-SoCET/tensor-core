`include "fust_g_if.vh"
`include "datapath_types.vh"

module fust_g (
    input logic CLK, nRST,
    fust_g_if.FUSTG fuif
);

  import datapath_pkg::*;

  fust_g_t fust;
  
  always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST)
      fuif.fust <= '0;
    else
      fuif.fust <= fust;
  end

  always_comb begin
    fust = fuif.fust;
   
    fust.op = fuif.en ? fuif.fust_row : fuif.fust.op;
  end

endmodule
