// Interfaces
`include "datapath_types.vh"
`include "fu_branch_if.vh"
`include "fu_alu_if.vh"
`include "fu_scalar_ls_if.vh"
`include "fu_matrix_ls_if.vh"
`include "fu_gemm_if.vh"

module execute (
    input logic CLK, nRST,
    execute_if.eif eif
);

// shared signals immediate
// Interfaces
fu_matrix_ls_if.mls mlsif();
fu_branch_if.btb fubif();
fu_alu_if.alu aluif();
fu_scalar_ls_if.sls slsif();
fu_gemm_if.GEMM fugif();

// Branch FU
fu_branch BFU(CLK, nRST, eif.ihit, fubif);
assign fubif.branch_outcome = eif.bfu_branch_outcome;
assign fubif.update_btb = eif.bfu_update_btb;
assign fubif.branch_target = eif.bfu_branch_target;
assign fubif.pc = eif.bfu_pc;
assign fubif.pc_fetch = eif.bfu_pc_fetch;
// Outputs: pred_outcome, hit, pred_target
assign eif.bfu_pred_outcome = fubif.pred_outcome;
assign eif.bfu_hit = fubif.hit;
assign eif.bfu_pred_target = fubif.pred_target;


// Scalar ALU FU
fu_alu SALU(aluif);
assign aluif.aluop = eif.salu_aluop;
assign aluif.port_a = eif.salu_port_a;
assign aluif.port_b = eif.salu_port_b;
// Outputs
assign eif.salu_negative = aluif.negative;
assign eif.salu_overflow = aluif.overflow;
assign eif.salu_port_output = aluif.port_output;
assign eif.salu_zero = aluif.zero;

// Scalar Load/Store FU
fu_scalar_ls SLS(CLK, nRST, slsif);
assign slsif.imm = eif.imm;
assign slsif.mem_type = eif.sls_mem_type; // Load or store
assign slsif.rs1 = eif.sls_rs1;  // If load
assign slsif.rs2 = eif.sls_rs2; // Adding imm
assign slsif.dmem_in = eif.sls_dmem_in;
assign slsif.dhit_in = eif.sls_dhit_in;
// Outputs
assign eif.sls_dmemaddr = slsif.dmemaddr;
assign eif.sls_dmemREN = slsif.dmemREN;
assign eif.sls_dmemWEN = slsif.dmemWEN;
assign eif.sls_dmemstore = slsif.dmemstore;
assign eif.sls_dmemload = slsif.dmemload;
assign eif.sls_dhit = slsif.dhit;

// Matrix Load/Store FU
fu_matrix_ls MLS(mlsif);
assign mlsif.mhit = eif.mls_mhit;
assign mlsif.enable = eif.mls_enable;
assign mlsif.ls_in = eif.mls_ls_in;
assign mlsif.rd_in = eif.mls_rd_in;
assign mlsif.rs_in = eif.mls_rs_in;
assign mlsif.stride_in = eif.mls_stride_in;
assign mlsif.imm_in = eif.mls_imm_in;
// MLS Outputs
assign eif.mls_done = mlsif.done;
assign eif.mls_ls_out = mlsif.ls_out;
assign eif.mls_rd_out = mlsif.rd_out;
assign eif.mls_address = mlsif.address;
assign eif.mls_stride_out = mlsif.stride_out;

// GEMM FU
fu_gemm GEMM(CLK, nRST, fugif);
assign fugif.fetch_p = eif.gemm_fetch_p;
assign fugif.flush = eif.gemm_flush;
assign fugif.freeze = eif.gemm_freeze;
// Outputs
assign eif.gemm_rs1 = fugif.rs1;
assign eif.gemm_rs2 = fugif.rs2;
assign eif.gemm_rs3 = fugif.rs3;
assign eif.gemm_rd = fugif.rd;

endmodule