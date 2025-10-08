// Mask Unit Module +++++++++++============================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Mask unit that sends specific mask bits to lanes
// ========================================================================
`include "vector_if.vh"
`include "vector_types.vh"

module masku (
    vector_if.masku vif
);
    import vector_pkg::*;

    logic [NUM_ELEMENTS-1:0] vmask;

    always_comb begin : Extract_Mask
        vmask = '0;
        if (vif.masku_in.vm == 1'b0) begin
            vmask = '1; 
        end else begin
            for (int i = 0; i < NUM_ELEMENTS; i++) begin
                if (vif.masku_in.vl < i) begin
                    vmask[i] = 1'b0; 
                end 
                else begin
                    vmask[i] = logic'(vif.masku_in.vmask[i][vif.masku_in.imm]);
                end
            end
        end
    end

    assign vif.masku_out.mask = vmask;
endmodule