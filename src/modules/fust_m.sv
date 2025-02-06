`include "fust_m_if.vh"
`include "datapath_types.vh"

module fust_m (
    input logic CLK, nRST,
    fust_m_if.FUSTM fuif
);

  import datapath_pkg::*;

  fust_m_t fust;
  
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
