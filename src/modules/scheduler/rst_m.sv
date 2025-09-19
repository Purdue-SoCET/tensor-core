`include "rst_m_if.vh"
`include "datapath_types.vh"

module rst_m (
    input logic CLK, nRST,
    rst_m_if.RSTM rsif
);

  import datapath_pkg::*;

  rst_m_t status;
  
  always_ff @(negedge CLK, negedge nRST) begin
    if (~nRST)
      rsif.status <= '0;
    else
      rsif.status <= status;
  end

  always_comb begin
    status = rsif.status;

    if (rsif.di_write) begin //assumes dispatch reads the state is IDLE
      status.idx[rsif.di_sel].busy = 1;
      status.idx[rsif.di_sel].tag = rsif.di_tag;
    end
    if (rsif.wb_write) begin
      status.idx[rsif.wb_sel].busy = 0;
      status.idx[rsif.wb_sel].tag = '0;
    end
  end

endmodule
