// PIPELINE PACKAGES
`include "datapath_types.vh"

// INTERFACES
`include "fetch_stage_if.vh"
`include "scoreboard_if.vh"
`include "dispatch_if.vh"
`include "issue_if.vh"
`include "regfile_if.vh"
`include "execute_if.vh"
`include "writeback_if.vh"
`include "datapath_cache_if.vh"


module sc_datapath
(
    input logic CLK, nrst,
    datapath_cache_if.dp dcif
);
    fetch_stage_if fif();
    fetch_stage FETCH (CLK, nrst, dcif.ihit, fif);

    scoreboard_if sbif();
    scoreboard SCOREBOARD (CLK, nrst, sbif);

    execute_if eif();
    execute EXECUTE (CLK, nrst, eif);

    writeback_if wbif();
    writeback WRITEBACK (CLK, nrst, wbif);

    // total dp inputs and outputs
    // input   ihit, imemload, dhit, dmemload
    // output  halt, imemREN, imemaddr, dmemREN, dmemWEN, dmemstore, dmemaddr

    // IMPORT PACKAGE
    import isa_pkg::*;
    import datapath_pkg::*;

    // LATCH INSTANTIATIONS
    fetch_t fetch_out;
    fetch_t sb_in;
 
    // issue_t sbif.out;
    // issue_t sbif.out;

    execute_t ex_out;
    execute_t wb_in;

    assign dcif.halt = eif.eif_output.halt;
    // assign dcif.imemREN = 1;
    // assign dcif.imemaddr = fif.pc;

    // fetch signals
    // TODO 
    // - all the input signals from execute to fetch combinationally
    // - check the mem signals are correct to fetch
    // - the outputs of fetch should be set to the inputs of the fetch -> sb latch

    // input
    assign fif.imemload        = dcif.imemload;  // from mem
    assign fif.freeze          = sbif.freeze || sbif.jump;
    assign fif.misprediction   = eif.eif_output.bfu_miss;
    assign fif.correct_pc      = eif.eif_output.bfu_correct_pc;
    assign fif.update_btb      = eif.eif_output.bfu_update_btb;
    assign fif.branch_outcome  = eif.eif_output.bfu_branch_outcome;
    assign fif.update_pc       = eif.eif_output.bfu_update_pc;
    assign fif.branch_target   = eif.eif_output.bfu_branch_target;

    // output 
    assign fetch_out.imemload  = fif.instr;
    assign fetch_out.br_pc     = fif.pc;
    assign fetch_out.br_pred   = fif.predicted_outcome;
    assign dcif.imemaddr       = fif.imemaddr;  // to mem
    assign dcif.imemREN        = fif.imemREN;   // to mem


    // sb signals

    // inputs
    assign sbif.fetch                 = sb_in;
    assign sbif.wb_issue              = wbif.wb_out;
    assign sbif.wb_dispatch.s_rw_en   = wbif.wb_out.reg_en;
    assign sbif.wb_dispatch.s_rw      = wbif.wb_out.reg_sel;
    assign sbif.wb_dispatch.m_rw_en   = '0; // these need logc from memory, saying m_reg can be cleared from rsts
    assign sbif.wb_dispatch.m_rw      = '0; // these need logc from memory, saying which m_reg can be cleared from rsts
    assign sbif.branch_miss           = eif.eif_output.bfu_miss;
    assign sbif.branch_resolved       = eif.eif_output.bfu_resolved;
    assign sbif.fu_ex                 = eif.eif_output.fu_ex;

    // outputs
    // assign sb_out = sbif.out;


    // execute signals

    // inputs
    assign eif.rd = sbif.out.rd;
    assign eif.spec = sbif.out.spec;
    assign eif.halt = sbif.out.halt;
    // branch
    // assign eif.bfu_branch = ? not sure what this is and where it should be coming from
    assign eif.bfu_enable              = sbif.out.fu_en[2];
    assign eif.bfu_branch_type         = sbif.out.branch_type;
    assign eif.bfu_reg_a               = sbif.out.rdat1;
    assign eif.bfu_reg_b               = sbif.out.rdat2;
    assign eif.bfu_current_pc          = sbif.out.branch_pc;
    assign eif.bfu_imm                 = sbif.out.imm;
    assign eif.bfu_predicted_outcome   = sbif.out.branch_pred_pc;
    assign eif.bfu_j_type              = sbif.out.j_type;
    // alu
    assign eif.salu_aluop   = sbif.out.alu_op;
    assign eif.salu_port_a  = sbif.out.rdat1;
    assign eif.salu_port_b  = sbif.out.rdat2;
    assign eif.salu_enable  = sbif.out.fu_en[0];
    // scalar ls
    assign eif.sls_enable    = sbif.out.fu_en[1];
    assign eif.sls_imm       = sbif.out.imm;
    assign eif.sls_rs1       = sbif.out.rdat1;
    assign eif.sls_rs2       = sbif.out.rdat2;
    assign eif.sls_mem_type  = sbif.out.mem_type;
    assign eif.sls_dmem_in   = dcif.dmemload; // from mem
    assign eif.sls_dhit_in   = dcif.dhit;     // from mem
    // matrix ls
    assign eif.mls_enable     = sbif.out.fu_en[3];
    assign eif.mls_mhit       = dcif.mhit;
    assign eif.mls_ls_in      = sbif.out.ls_in;
    assign eif.mls_rd_in      = sbif.out.md;
    assign eif.mls_rs_in      = sbif.out.rdat1;
    assign eif.mls_stride_in  = sbif.out.rdat2;
    assign eif.mls_imm_in     = sbif.out.imm;
    // gemm
    assign eif.gemm_enable         = sbif.out.fu_en[4];
    assign eif.gemm_done           = dcif.gemm_done;
    assign eif.gemm_new_weight_in  = sbif.out.gemm_new_weight;
    assign eif.gemm_rd_in          = sbif.out.md;
    assign eif.gemm_rs1_in         = sbif.out.ms1;
    assign eif.gemm_rs2_in         = sbif.out.ms2;
    assign eif.gemm_rs3_in         = sbif.out.ms3;

    // ouputs
    assign ex_out.alu_done      = eif.eif_output.fu_ex[0] && !eif.eif_output.bfu_miss;
    assign ex_out.alu_wdat      = eif.eif_output.salu_port_output;
    assign ex_out.alu_reg_sel   = eif.eif_output.salu_rd;
    assign ex_out.load_done     = (eif.eif_output.sls_dhit == dhit_load);
    assign ex_out.load_wdat     = eif.eif_output.sls_dmemload;
    assign ex_out.load_reg_sel  = eif.eif_output.sls_rd;
    assign ex_out.spec          = eif.eif_output.spec;
    assign ex_out.jump_done     = eif.eif_output.fu_ex[2];
    assign ex_out.jump_wdat     = eif.eif_output.jump_wdat;
    assign ex_out.jump_reg_sel  = eif.eif_output.jump_rd;

    assign dcif.dmemWEN    = eif.eif_output.sls_dmemWEN;
    assign dcif.dmemREN    = eif.eif_output.sls_dmemREN;
    assign dcif.dmemstore  = eif.eif_output.sls_dmemstore;
    assign dcif.dmemaddr   = eif.eif_output.sls_dmemaddr;

    assign dcif.matrix_ls  = eif.eif_output.fu_matls_out;

    assign dcif.gemm_out   = eif.eif_output.gemm_out;



    // wb signals

    // inputs
    assign wbif.alu_wdat           = wb_in.alu_wdat;
    assign wbif.load_wdat          = wb_in.load_wdat;
    assign wbif.jump_wdat          = wb_in.jump_wdat;
    assign wbif.branch_mispredict  = eif.eif_output.bfu_miss;
    assign wbif.branch_spec        = wb_in.spec;
    assign wbif.branch_correct     = eif.eif_output.bfu_resolved;
    assign wbif.alu_done           = wb_in.alu_done;
    assign wbif.load_done          = wb_in.load_done;
    assign wbif.jump_done          = wb_in.jump_done;
    assign wbif.alu_reg_sel        = wb_in.alu_reg_sel;
    assign wbif.load_reg_sel       = wb_in.load_reg_sel;
    assign wbif.jump_reg_sel       = wb_in.jump_reg_sel;


    // FLIP-FLOP FOR LATCHES
    always_ff @(posedge CLK, negedge nrst) begin
        if (!nrst) begin
            sb_in <= '0;
            // ex_in <= '0;
            wb_in <= '0;
        end
        else begin
            sb_in <= fetch_out;
            // ex_in <= sb_out;
            wb_in <= ex_out;
        end
    end

endmodule
