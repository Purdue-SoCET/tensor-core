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

    logic gemm_edge, mls_edge;
    // shared signals immediate
    // Interfaces
    fu_matrix_ls_if mlsif();
    fu_branch_if fubif();
    fu_alu_if aluif();
    fu_scalar_ls_if slsif();
    fu_gemm_if fugif();

    // halt needs to get passed into memory
    assign eif.eif_output.halt = eif.halt; // to mem 

    // spec needs to get passed to wb
    assign eif.eif_output.spec = eif.spec; // to wb

    // Branch FU
    fu_branch BFU(CLK, nRST, fubif);
    // assign fubif.branch = eif.bfu_branch; // is this enable? coming from btb or sb?
    assign fubif.enable = eif.bfu_enable; // from sb
    assign fubif.branch_type = eif.bfu_branch_type; // from sb
    // assign fubif.branch_gate_sel = eif.bfu_branch_gate_sel; // have this just done in the branch fu
    assign fubif.reg_a = eif.bfu_reg_a; // from sb
    assign fubif.reg_b = eif.bfu_reg_b; // from sb
    assign fubif.current_pc = eif.bfu_current_pc; // from sb
    assign fubif.imm = eif.bfu_imm; // from sb
    assign fubif.predicted_outcome = eif.bfu_predicted_outcome; // from sb
    assign fubif.j_type = eif.bfu_j_type;
    // Outputs: branch_outcome, updated_pc, miss, correct_pc, update_btb, update_pc, branch_target
    // lines 37 to 42, can you (argha) say where these go to, like how outputs are labeled in other functional units
    assign eif.eif_output.bfu_branch_outcome = fubif.branch_outcome; // to fetch 
    // assign eif.eif_output.bfu_updated_pc = fubif.updated_pc; // to fetch
    assign eif.eif_output.bfu_correct_pc = fubif.correct_pc; // to fetch
    assign eif.eif_output.bfu_update_btb = fubif.update_btb; // to fetch
    assign eif.eif_output.bfu_update_pc = fubif.update_pc; // to fetch
    assign eif.eif_output.bfu_branch_target = fubif.branch_target; // to fetch
    assign eif.eif_output.bfu_miss = fubif.miss; // to fetch, sb, wb
    assign eif.eif_output.bfu_resolved = fubif.resolved; // to sb and wb
    assign eif.eif_output.fu_ex[2] = (fubif.resolved || fubif.miss); // to sb
    assign eif.eif_output.jump_rd = eif.rd;
    assign eif.eif_output.jump_wdat = fubif.jump_wdat; 
    assign eif.eif_output.br_jump = fubif.br_jump;
    // assign eif.eif_output.jump_dest = fubif.jump_dest; // might not need this, can just update using bfu_update_pc?

    // Scalar ALU FU
    fu_alu SALU(aluif);
    assign aluif.aluop = eif.salu_aluop; // from sb
    assign aluif.port_a = eif.salu_port_a; // from sb
    assign aluif.port_b = eif.salu_port_b; // from sb
    assign aluif.enable = eif.salu_enable; // from sb
    // Outputs 
    assign eif.eif_output.salu_negative = aluif.negative;       // needed?
    assign eif.eif_output.salu_overflow = aluif.overflow;       // needed?
    assign eif.eif_output.salu_zero = aluif.zero;               // needed?
    assign eif.eif_output.salu_port_output = aluif.port_output; // to wb
    assign eif.eif_output.fu_ex[0] = eif.salu_enable; // to sb and wb
    assign eif.eif_output.salu_rd = eif.rd; // to wb

    // Scalar Load/Store FU
    fu_scalar_ls SLS(CLK, nRST, slsif);
    assign slsif.enable = eif.sls_enable; // from dp
    assign slsif.imm = eif.sls_imm; // from dp
    assign slsif.mem_type = eif.sls_mem_type; // from dp
    assign slsif.rs1 = eif.sls_rs1; // from dp
    assign slsif.rs2 = eif.sls_rs2; // from dp
    assign slsif.dmem_in = eif.sls_dmem_in;   // from mem
    assign slsif.dhit_in = eif.sls_dhit_in;   // from mem
    assign slsif.rd_in = eif.rd; // from dp
    // Outputs
    assign eif.eif_output.sls_dmemaddr = slsif.dmemaddr; // to mem
    assign eif.eif_output.sls_dmemREN = slsif.dmemREN; // to mem
    assign eif.eif_output.sls_dmemWEN = slsif.dmemWEN; // to mem
    assign eif.eif_output.sls_dmemstore = slsif.dmemstore; // to mem
    assign eif.eif_output.sls_dmemload = slsif.dmemload; // to wb
    assign eif.eif_output.sls_dhit = slsif.dhit; // to wb - if dhit_load, wb
    assign eif.eif_output.fu_ex[1] = |slsif.dhit; // to sb 
    assign eif.eif_output.sls_rd = slsif.rd; // to wb

    // Matrix Load/Store FU
    fu_matrix_ls MLS(mlsif);
    // assign mlsif.mhit = eif.mls_mhit; // from mem (scratchpad)
    assign mlsif.enable = eif.mls_enable; // from sb
    assign mlsif.ls_in = eif.mls_ls_in; // from sb
    assign mlsif.rd_in = eif.mls_rd_in; // from sb
    assign mlsif.rs_in = eif.mls_rs_in; // from sb
    // assign mlsif.stride_in = eif.mls_stride_in; // from sb
    assign mlsif.imm_in = eif.mls_imm_in; // from sb
    // MLS Outputs
    // assign eif.eif_output.fu_matls_out = mlsif.fu_matls_out; 
    assign eif.eif_output.fu_ex[3] = eif.load_complete || eif.store_complete;
    // fu_matls_out struct
    // done         to sb
    // ls_out       to mem (scratchpad)
    // rd_out       to mem (scratchpad)
    // address      to mem (scratchpad)
    // stride_out   to mem (scratchpad)

    // GEMM FU
    fu_gemm GEMM(CLK, nRST, fugif);
    assign fugif.gemm_enable = eif.gemm_enable; // from sb
    assign fugif.new_weight_in = eif.gemm_new_weight_in; // from sb -> TODO: needs to be added, need a bit of clarification
    assign fugif.rs1_in = eif.gemm_rs1_in;  // from sb
    assign fugif.rs2_in = eif.gemm_rs2_in;  // from sb
    assign fugif.rs3_in = eif.gemm_rs3_in;  // from sb
    assign fugif.rd_in = eif.gemm_rd_in;    // from sb
    // Outputs
    /* Nick Changes: Outputs to Scratchpad FIFO Buff using my structs */
    
    // assign eif.eif_output.gemm_new_weight_out = eif.gemm_new_weight_in; // to mem (scratchpad)
    // assign eif.eif_output.gemm_matrix_num = fugif.gemm_matrix_num;    // to mem (scratchpad)
    // assign eif.eif_output.gemm_out = fugif.gemm_out; 
    // TODO: need some sort of done signal
    assign eif.eif_output.fu_ex[4] = eif.gemm_complete; 

    assign eif.eif_output.sp_out = (eif.mls_enable) ? mlsif.fu_matls_out : fugif.gemm_out;
    assign eif.eif_output.sp_write = ((eif.mls_enable && !mls_edge) || (eif.gemm_enable && !gemm_edge));

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            gemm_edge <= '0;
            mls_edge <= '0;
        end
        else begin
            gemm_edge <= eif.gemm_enable;
            mls_edge <= eif.mls_enable;
        end
    end

endmodule