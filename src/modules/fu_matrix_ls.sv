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
    mlsif.fu_matls_out = '0;
    if (mlsif.enable) begin     // LOAD STORE ENABLE
        if (mlsif.ls_in == M_LOAD) begin   // LOAD
            mlsif.fu_matls_out.ls_out.opcode = matrix_mem_t'(M_LOAD);
            mlsif.fu_matls_out.ls_out.ls_matrix_rd_gemm_new_weight = mlsif.rd_in;
            // mlsif.fu_matls_out.stride_out = mlsif.stride_in;
            mlsif.fu_matls_out.ls_out.ls_addr_gemm_gemm_sel = mlsif.rs_in + mlsif.imm_in;
        end

        else if (mlsif.ls_in == M_STORE) begin  // STORE
            mlsif.fu_matls_out.ls_out.opcode = matrix_mem_t'(M_STORE);
            mlsif.fu_matls_out.ls_out.ls_matrix_rd_gemm_new_weight = mlsif.rd_in;
            // mlsif.fu_matls_out.stride_out = mlsif.stride_in;
            mlsif.fu_matls_out.ls_out.ls_addr_gemm_gemm_sel = mlsif.rs_in + mlsif.imm_in;
        end
    end
end

endmodule