`include "fust_s_if.vh"
`include "datapath_types.vh"

module fust_s (
    input logic CLK, nRST,
    fust_s_if.FUSTS fuif
);

  import datapath_pkg::*;

  fust_s_t fust;
  
  always_ff @(posedge CLK, negedge nRST) begin
    if (~nRST) begin
      fuif.out_busy <= '0;
      fuif.out_t1 <= '0;
      fuif.out_t2 <= '0;
      fuif.out_op_alu <= '0;
      fuif.out_op_sls <= '0;
      fuif.out_op_br <= '0;
    end
    else begin
      fuif.out_busy <= fust.busy;
      fuif.out_t1 <= fust.t1;
      fuif.out_t2 <= fust.t2;
      fuif.out_op_alu <= fust.op[0];
      fuif.out_op_sls <= fust.op[1];
      fuif.out_op_br <= fust.op[2];
    end
  end

  always_comb begin
    // fust = fuif.fust;
    fust.op[0] = fuif.out_op_alu;
    fust.op[1] = fuif.out_op_sls;
    fust.op[2] = fuif.out_op_br;
    fust.busy = fuif.busy;
    fust.t1 = fuif.t1;
    fust.t2 = fuif.t2;

    if (fuif.en) begin
      fust.op[fuif.fu] = fuif.fust_row;
    end

    if (fuif.flush) begin
      for (int i = 0; i < 3; i++) begin
        if (fust.op[i].spec) begin
          fust.op = '0;
          fust.t1 = '0;
          fust.t2 = '0;
        end
      end
    end

    if (fuif.resolved) begin
      for (int i = 0; i < 3; i++) begin
        fust.op[i].spec = '0;
      end
    end

  end

endmodule
