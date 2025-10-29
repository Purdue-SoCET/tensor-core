`include "isa_types.vh"
`include "datapath_types.vh"
`include "fu_gemm_if.vh"

module fu_gemm(
    input logic CLK, 
    input logic nRST, 
    fu_gemm_if.GEMM fugif
);

logic ls_flag, nxt_ls_flag;
logic prev_rs1;

always_comb begin //if there is enable, and hit (mem is ready)
    fugif.gemm_matrix_num.rd = '0;
    fugif.gemm_matrix_num.rs1 = '0;
    fugif.gemm_matrix_num.rs2 = '0;
    fugif.gemm_matrix_num.rs3 = '0;
    fugif.new_weight_out = '0;

    if(fugif.gemm_enable) begin
        fugif.gemm_matrix_num.rd = fugif.rd_in;
        fugif.gemm_matrix_num.rs1 = fugif.rs1_in;
        fugif.gemm_matrix_num.rs2 = fugif.rs2_in;
        fugif.gemm_matrix_num.rs3 = fugif.rs3_in;
        fugif.new_weight_out = fugif.new_weight_in;
    end
end
endmodule