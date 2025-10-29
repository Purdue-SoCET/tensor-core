`include "vector_if.vh"
`include "vector_types.vh"

// Wrapper for masku: instantiates the combinational masku unit and
// registers its outputs into flip-flops (clocked by interface CLK).
module masku_wrapper (
    input CLK, nRST,
	vector_if.masku vif
);
	import vector_pkg::*;

	vector_if vif_int();

	assign vif_int.masku_in = vif.masku_in;
	masku dut (.vif(vif_int));

    logic [NUM_LANES-1:0][SLICE_W-1:0] mask_reg;

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST)
            mask_reg <= '0;
        else
            mask_reg <= vif.masku_in.vmask;
    end

    assign vif.masku_out.mask = mask_reg;

endmodule

