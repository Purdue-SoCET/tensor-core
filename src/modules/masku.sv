// Mask Unit Module +++++++++++============================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Mask unit that sends specific mask bits to lanes
// ========================================================================
`include "vector_if.vh"
//`include "vector_types.vh"

module masku (
    vector_if.masku vif
);
    import vector_pkg::*;

    genvar l;
    generate
        for (l = 0; l < NUM_LANES; l++) begin : g_lane_mask
            assign vif.masku_out.mask[l] = vif.masku_in.vmask[l*SLICE_W +: SLICE_W];
        end
    endgenerate

endmodule
