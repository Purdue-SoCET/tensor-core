// Operand Buffer Module ==================================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Operand Buffer to keep read values during conflict
// ========================================================================
`include "vector_if.vh"
`include "vector_types.vh"

module op_buffer (
    input  logic CLK, nRST,
    vector_if.op_buffer vif
);
    import vector_pkg::*;

    vmask_t [MASK_PORTS-1:0] vmask_tmp;
    vreg_t  [READ_PORTS-1:0] vreg_tmp;
    logic   [MASK_PORTS-1:0] buf_full;
    logic   [MASK_PORTS-1:0] in_gvalid;

    always_comb begin
        for (int i = 0; i < MASK_PORTS; i++)
            in_gvalid[i] = vif.opbuff_in.dvalid[2*i] &
                           vif.opbuff_in.dvalid[2*i+1] &
                           vif.opbuff_in.mvalid[i];
    end

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin 
            vmask_tmp <= '{default:'0};
            vreg_tmp  <= '{default:'0};
            buf_full  <= '0;
        end else begin 
            if (!vif.opbuff_in.ready) begin
                for (int i = 0; i < MASK_PORTS; i++) begin 
                    if (in_gvalid[i] && !buf_full[i]) begin
                        vmask_tmp[i]    <= vif.opbuff_in.vmask[i];
                        vreg_tmp[2*i]   <= vif.opbuff_in.vreg[2*i];
                        vreg_tmp[2*i+1] <= vif.opbuff_in.vreg[2*i+1];
                        buf_full[i]     <= 1'b1;
                    end
                end
            end
            if (vif.opbuff_in.ready) begin
                for (int i = 0; i < MASK_PORTS; i++)
                    if (buf_full[i]) buf_full[i] <= 1'b0;
            end
        end
    end

    int g;
    always_comb begin
        for (int i = 0; i < MASK_PORTS; i++) begin
            vif.opbuff_out.ivalid[i] = buf_full[i] ? 1'b1 : in_gvalid[i];
            vif.opbuff_out.vmask[i]  = buf_full[i] ? vmask_tmp[i]
                                                   : vif.opbuff_in.vmask[i];
        end
        for (int i = 0; i < READ_PORTS; i++) begin 
            g = i/2;
            vif.opbuff_out.vreg[i] = buf_full[g] ? vreg_tmp[i]
                                                 : vif.opbuff_in.vreg[i];
        end 
    end
endmodule