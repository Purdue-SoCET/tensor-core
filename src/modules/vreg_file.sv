// vreg_file.sv — minimal wrapper using interface modport
`include "vector_if.vh"
`include "vector_types.vh"

module vreg_file (
  vector_if vif
);
  import vector_pkg::*;

  veggie veggie (
    .CLK (vif.CLK),
    .nRST(vif.nRST),
    .vif (vif.veggie)
  );

  always_comb begin
    vif.opbuff_in.vreg   = vif.veggie_out.vreg;
    vif.opbuff_in.dvalid = vif.veggie_out.dvalid;
    vif.opbuff_in.vmask  = vif.veggie_out.vmask;
    vif.opbuff_in.mvalid = vif.veggie_out.mvalid;
    vif.opbuff_in.ready  = vif.iready;

    vif.vrf_ready        = vif.veggie_out.ready;
  end

  op_buffer u_op_buffer (
    .CLK (vif.CLK),
    .nRST(vif.nRST),
    .vif (vif.op_buffer) 
  );

endmodule
