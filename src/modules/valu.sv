`include "vector_if.vh"
`include "vector_types.vh"
 
 module vector_alu (
  input logic CLK, nRST,
  vector_if.valu vif
 );
  import vector_pkg::*;

    always_comb begin : FP16_SPECIALCASES
      // Zero
      if (vif.vdat1.exp == 5'd0 && vif.vdat1.frac == 10'd0) begin

      end

      // Subnormal
      if (vif.vdat1.exp == 5'd0 && vif.vdat1.frac != 10'd0) begin

      end

      // Inf
      if (vif.vdat1.exp == 5'd255 && vif.vdat1.frac == 10'd0) begin

      end

      // NaN
      if (vif.vdat1.exp == 5'd255 && vif.vdat1.frac != 10'd0) begin

      end
    end
    
    genvar lane;
    generate
      for (lane = 0; lane < NUM_ELEMENTS; lane++) begin : GEN_LANES
        always_comb begin : VALU_LANE
          if (!vif.vm || vif.vmask[lane]) begin
            casez (vif.vop)
                VALU_ADD: begin
                  vif.result[lane] = vfpadd(vif.vdat1[lane], vif.vdat2[lane]);
                end 
                VALU_SUB: begin
                  vif.vdat2[lane].sign = ~vif.vdat2[lane].sign;
                  vif.result[lane] = vfpadd(vif.vdat1[lane], vif.vdat2[lane]);
                end

                default: vif.result[lane] = '0;
            endcase
          end
        end
      end
    endgenerate
 endmodule
