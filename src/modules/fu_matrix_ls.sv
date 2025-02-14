/* FU Matrix LS Code */

`include "datapath_types.vh"
`include "isa_types.vh"
`include "fu_matrix_ls_if.vh"

module fu_matrix_ls
(
    fu_matrix_ls_if.mls mlsif // MATRIX LOAD STORE IF
);

// importing types
import datapath_pkg::*;
import isa_pkg::*;

assign mlsif.fu_matls_out.done = mlsif.mhit; // Mhit

always_comb begin : LOAD_STORE
    if (mlsif.enable) begin     // LOAD STORE ENABLE
        if (mlsif.ls_in[0]) begin   // LOAD
            mlsif.fu_matls_out.ls_out[0] = 1;
            mlsif.fu_matls_out.rd_out = mlsif.rd_in;
            mlsif.fu_matls_out.stride_out = mlsif.stride_in;
            mlsif.fu_matls_out.address = mlsif.rs_in + mlsif.imm_in;
        end

        else if (mlsif.ls_in[1]) begin  // STORE
            mlsif.fu_matls_out.ls_out[1] = 1;
            mlsif.fu_matls_out.rd_out = mlsif.rs_in;
            mlsif.fu_matls_out.stride_out = mlsif.stride_in;
            mlsif.fu_matls_out.address = mlsif.rd_in + mlsif.imm_in;
        end
    end
end

endmodule