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
        fugif.gemm_out.mat_op = M_GEMM;
        fugif.gemm_out.mat_rd = {fugif.new_weight_in, 3'd0};
        fugif.gemm_out.mat_addr = {16'd0, fugif.rd_in, fugif.rs1_in, fugif.rs2_in, fugif.rs3_in};
    end
end
endmodule