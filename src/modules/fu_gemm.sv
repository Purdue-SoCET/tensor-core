`include "isa_types.vh"
`include "datapath_types.vh"
`include "fu_gemm_if.vh"

module fu_gemm(
    input logic CLK, 
    input logic nRST, 
    fu_gemm_if.GEMM fugif
);

// importing types
import datapath_pkg::*;
import isa_pkg::*;
// logic ls_flag, nxt_ls_flag;
// logic prev_rs1;

always_comb begin //if there is enable, and hit (mem is ready)
    fugif.gemm_out = '0;
    if(fugif.gemm_enable) begin
        fugif.gemm_out.opcode = matrix_mem_t'(M_GEMM);
        fugif.gemm_out.ls_matrix_rd_gemm_new_weight = {fugif.new_weight_in, '0};
        fugif.gemm_out.ls_addr_gemm_gemm_sel = {'0, fugif.rd_in, fugif.rs1_in, fugif.rs2_in, fugif.rs3_in};
    end
end
endmodule