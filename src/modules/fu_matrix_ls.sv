/* FU Matrix LS Code */

`include "cpu_types_pkg.vh"
`include "fu_matrix_ls_if.vh"

module fu_matrix_ls
(
    fu_matrix_ls_if.mls mlsif // MATRIX LOAD STORE IF
);

// importing types
import cpu_types_pkg::*;

assign mlsif.done = mlsif.mhit; // Mhit

always_comb begin : LOAD_STORE
    if (mlsif.enable) begin     // LOAD STORE ENABLE
        if (mlsif.ls_in[0]) begin   // LOAD
            mlsif.ls_out[0] = 1;
            mlsif.rd_out = mlsif.rd_in;
            mlsif.rs_out = mlsif.rs_in;
            mlsif.stride_out = mlsif.stride_in;
            mlsif.imm_in = mlsif.imm_out
        end

        else if (mlsif.ls_in[1]) begin  // STORE
            mlsif.ls_out[1] = 1;
            mlsif.rd_out = mlsif.rd_in;
            mlsif.rs_out = mlsif.rs_in;
            mlsif.stride_out = mlsif.stride_in;
            mlsif.imm_in = mlsif.stride_in;
        end
    end
end

endmodule