// Interfaces
`include "datapath_types.vh"
`include "fu_branch_if.vh"
`include "fu_alu_if.vh"
`include "fu_scalar_ls_if.vh"
`include "fu_matrix_ls_if.vh"
`include "fu_gemm_if.vh"
`include "execute_if.vh"

module execute (
    input logic CLK, nRST,
    execute_if.eif eif
);

// shared signals immediate
// Interfaces
fu_matrix_ls_if mlsif();
fu_branch_if fubif();
fu_alu_if aluif();
fu_scalar_ls_if slsif();
fu_gemm_if fugif();


// Branch FU
fu_branch BFU(CLK, nRST, fubif);
assign fubif.branch = eif.bfu_branch; // is this enable?
assign fubif.enable = eif.bfu_enable;
assign fubif.branch_type = eif.bfu_branch_type;
// assign fubif.branch_gate_sel = eif.bfu_branch_gate_sel; // have this just done in the branch pred
assign fubif.reg_a = eif.bfu_reg_a;
assign fubif.reg_b = eif.bfu_reg_b;
assign fubif.current_pc = eif.bfu_current_pc;
assign fubif.imm = eif.bfu_imm;
assign fubif.predicted_outcome = eif.bfu_predicted_outcome;
// Outputs: branch_outcome, updated_pc, misprediction, correct_pc, update_btb, update_pc, branch_target
assign eif.eif_output.bfu_branch_outcome = fubif.branch_outcome;
assign eif.eif_output.bfu_updated_pc = fubif.updated_pc; 
assign eif.eif_output.bfu_misprediction = fubif.misprediction;
assign eif.eif_output.bfu_correct_pc = fubif.correct_pc;
assign eif.eif_output.bfu_update_pc = fubif.update_pc;
assign eif.eif_output.bfu_branch_target = fubif.branch_target;

// Scalar ALU FU
fu_alu SALU(aluif);
assign aluif.aluop = eif.salu_aluop;
assign aluif.port_a = eif.salu_port_a;
assign aluif.port_b = eif.salu_port_b;
// Outputs
assign eif.eif_output.salu_negative = aluif.negative;
assign eif.eif_output.salu_overflow = aluif.overflow;
assign eif.eif_output.salu_port_output = aluif.port_output;
assign eif.eif_output.salu_zero = aluif.zero;

// Scalar Load/Store FU
fu_scalar_ls SLS(CLK, nRST, slsif);
assign slsif.imm = eif.sls_imm;
assign slsif.mem_type = eif.sls_mem_type; // Load or store
assign slsif.rs1 = eif.sls_rs1;  // If load
assign slsif.rs2 = eif.sls_rs2; // Adding imm
assign slsif.dmem_in = eif.sls_dmem_in;
assign slsif.dhit_in = eif.sls_dhit_in;
// Outputs
assign eif.eif_output.sls_dmemaddr = slsif.dmemaddr;
assign eif.eif_output.sls_dmemREN = slsif.dmemREN;
assign eif.eif_output.sls_dmemWEN = slsif.dmemWEN;
assign eif.eif_output.sls_dmemstore = slsif.dmemstore;
assign eif.eif_output.sls_dmemload = slsif.dmemload;
assign eif.eif_output.sls_dhit = slsif.dhit;

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
assign eif.eif_output.fu_matls_out = mlsif.fu_matls_out;

// GEMM FU
fu_gemm GEMM(CLK, nRST, fugif);
assign fugif.gemm_enable = eif.gemm_enable;
assign fugif.new_weight_in = eif.gemm_new_weight_in;
assign fugif.rs1_in = eif.gemm_rs1_in;
assign fugif.rs2_in = eif.gemm_rs2_in; 
assign fugif.rs3_in = eif.gemm_rs3_in;
assign fugif.rd_in = eif.gemm_rd_in;
// Outputs
assign eif.eif_output.gemm_new_weight_out = fugif.new_weight_out;
assign eif.eif_output.gemm_matrix_num = fugif.gemm_matrix_num;


endmodule