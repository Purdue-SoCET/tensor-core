`include "datapath_types.vh"
`include "dispatch_if.vh"
`include "control_unit_if.vh"
`include "control_unit.sv"
`include "rst_s.sv"
`include "rst_m.sv"
`include "rst_s_if.vh"
`include "rst_m_if.vh"

module dispatch(
    input logic CLK, nRST,
    dispatch_if.DI diif
);

    import isa_pkg::*;
    import datapath_pkg::*;

    // Instantiations
    control_unit_if cuif();
    rst_s_if rstsif();
    rst_m_if rstmif();

    control_unit CU(cuif);
    rst_s RSTS(CLK, nRST, rstsif);
    rst_m RSTM(CLK, nRST, rstmif);

    // Local Variables
    logic WAW;
    logic s_busy;
    logic m_busy;
    logic hazard;
    logic [WORD_W-1:0] instr;
    regbits_t s_rd, s_rs1, s_rs2;
    matbits_t m_rd, m_rs1, m_rs2, m_rs3;
    logic flush;
    dispatch_t n_dispatch;
    dispatch_t dispatch;

    always_ff @ (posedge CLK, negedge nRST) begin: Pipeline_Latching
      if (~nRST)
        diif.out <= '0;
    	else
        diif.out <= n_dispatch;
    end

    assign flush = diif.flush & diif.ihit;
    always_comb begin : Pipeline_Output
      case (1'b1)
        flush:       n_dispatch = '0;
        diif.freeze: n_dispatch = diif.out;
        hazard:      n_dispatch = diif.out;
        default:     n_dispatch = dispatch; // i dont think we need to advance only on ihit
      endcase
    end

    always_comb begin: Instr_Signals
      instr = diif.fetch.imemload;
      s_rd = instr[11:7];
      s_rs1 = instr[19:15];
      s_rs2 = instr[24:20];
      m_rd = instr[31:28];
      m_rs1 = instr[27:24];
      m_rs2 = instr[23:20];
      m_rs3 = instr[19:16];
    end

    always_comb begin : Control_Unit
      cuif.instr = instr;
    end

    always_comb begin : Hazard_Logic
      case (cuif.fu_s)
        FU_S_ALU:     s_busy = diif.fust_s.busy[FU_S_ALU];
        FU_S_LD_ST:   s_busy = diif.fust_s.busy[FU_S_LD_ST];
        FU_S_BRANCH:  s_busy = diif.fust_s.busy[FU_S_BRANCH];
        default: s_busy = 1'b0;
      endcase
      case (cuif.fu_m)
        FU_M_LD_ST: m_busy = diif.fust_m.busy;
        FU_M_GEMM:    m_busy = diif.fust_g.busy;
        default: m_busy = 1'b0;
      endcase

      WAW = (cuif.m_mem_type == M_LOAD | cuif.fu_m == FU_M_GEMM) ? rstmif.status.idx[m_rd].busy : 
            (cuif.s_reg_write) ? rstsif.status.idx[s_rd].busy: 1'b0;
      hazard = (s_busy | m_busy | WAW); //TODO: remember to tie this hazard back to stall the fetch to not squash this stage on a hazard
    end

    always_comb begin : Reg_Status_Tables
      init_rst();

      // only write to Reg Status Table if doing a regwrite,
      // and the instruction is actually moving forward
      rstsif.di_write = 1'b0;
      if (cuif.s_reg_write) begin
        if (~hazard & ~flush & ~diif.freeze) begin // hazard a little strange, will need to take a look going forward
          rstsif.di_sel = s_rd;
          rstsif.di_write = 1'b1;
          rstsif.di_tag = (cuif.fu_s == FU_S_LD_ST) ? 2'd2 : 2'd1; // 1 for ALU, 2 for LD
        end
      end

      // maybe add a m_reg_write in cuif to simplify
      if (cuif.m_mem_type == M_LOAD | cuif.fu_m == FU_M_GEMM) begin
        if (~hazard & ~flush & ~diif.freeze) begin
          rstmif.di_sel = m_rd;
          rstmif.di_write = 1'b1;
          rstmif.di_tag = (cuif.fu_m == FU_M_LD_ST) ? 2'd2 : 2'd1; // 1 for GEMM, 2 for LD
        end
      end
      
      // writeback needs to update the RST on commits
      if (diif.wb.s_rw_en) begin
        rstsif.wb_sel = diif.wb.s_rw;
        rstsif.wb_write = '1;
        // rstsif.wb_write = '0;
      end

      if (diif.wb.m_rw_en) begin
        rstmif.wb_sel = diif.wb.m_rw;
        rstmif.wb_write = '1;
        // rstmif.wb_write = '0;
      end
    end

    always_comb begin : FUST
      diif.n_fu_t = cuif.fu_t;
      diif.n_t1 = diif.fust_s.t1;
      diif.n_t2 = diif.fust_s.t2;

      // tag updates on WB
      if (diif.wb.s_rw_en & diif.wb.alu_done & diif.fust_state[0] == FUST_EX) begin
        diif.n_t1[FU_S_LD_ST] = (diif.fust_s.t1[FU_S_LD_ST] == 2'd1) && diif.fust_s.busy[FU_S_LD_ST] ? '0 : diif.fust_s.t1[FU_S_LD_ST];
        diif.n_t2[FU_S_LD_ST] = (diif.fust_s.t2[FU_S_LD_ST] == 2'd1) && diif.fust_s.busy[FU_S_LD_ST] ? '0 : diif.fust_s.t2[FU_S_LD_ST];
        diif.n_t1[FU_S_BRANCH] = (diif.fust_s.t1[FU_S_BRANCH] == 2'd1) && diif.fust_s.busy[FU_S_BRANCH] ? '0 : diif.fust_s.t1[FU_S_BRANCH];
        diif.n_t2[FU_S_BRANCH] = (diif.fust_s.t2[FU_S_BRANCH] == 2'd1) && diif.fust_s.busy[FU_S_BRANCH] ? '0 : diif.fust_s.t2[FU_S_BRANCH];
      end else if (diif.wb.s_rw_en & diif.wb.alu_done & diif.fust_state[1] == FUST_EX) begin
        diif.n_t1[FU_S_ALU] = (diif.fust_s.t1[FU_S_ALU] == 2'd2) && diif.fust_s.busy[FU_S_ALU] ? '0 : diif.fust_s.t1[FU_S_ALU];
        diif.n_t2[FU_S_ALU] = (diif.fust_s.t2[FU_S_ALU] == 2'd2) && diif.fust_s.busy[FU_S_ALU] ? '0 : diif.fust_s.t2[FU_S_ALU];
        diif.n_t1[FU_S_BRANCH] = (diif.fust_s.t1[FU_S_BRANCH] == 2'd2) && diif.fust_s.busy[FU_S_BRANCH] ? '0 : diif.fust_s.t1[FU_S_BRANCH];
        diif.n_t2[FU_S_BRANCH] = (diif.fust_s.t2[FU_S_BRANCH] == 2'd2) && diif.fust_s.busy[FU_S_BRANCH] ? '0 : diif.fust_s.t2[FU_S_BRANCH];
      end

      // To Issue **Combinationally**
      diif.n_fust_s_en   = (cuif.fu_t == FU_S_T & ~diif.flush & ~diif.freeze & ~hazard);
      diif.n_fu_s        = cuif.fu_s;
      diif.n_fust_s.rd   = s_rd;
      diif.n_fust_s.rs1  = s_rs1;
      diif.n_fust_s.rs2  = s_rs2;
      diif.n_fust_s.imm  = cuif.imm;
      diif.n_t1[cuif.fu_s]   = rstsif.status.idx[s_rs1].tag;
      diif.n_t2[cuif.fu_s]   = rstsif.status.idx[s_rs2].tag;

      diif.n_fust_m_en   = (cuif.fu_t == FU_M_T & ~flush & ~diif.freeze & ~hazard);
      //n_fu_m           = 1'b0; // only one row in FUST
      diif.n_fust_m.rd   = m_rd;
      diif.n_fust_m.rs1  = s_rs1;
      diif.n_fust_m.rs2  = s_rs2;
      diif.n_fust_m.imm  = cuif.imm[10:0];
      diif.n_fust_m.t1   = rstsif.status.idx[s_rs1].tag;
      diif.n_fust_m.t2   = rstsif.status.idx[s_rs2].tag;

      diif.n_fust_g_en   = (cuif.fu_t == FU_G_T & ~flush & ~diif.freeze & ~hazard);
      //n_fu_g           = 1'b0; // only one row in FUST
      diif.n_fust_g.rd   = m_rd;
      diif.n_fust_g.ms1  = m_rs1;
      diif.n_fust_g.ms2  = m_rs2;
      diif.n_fust_g.ms3  = m_rs3;
      diif.n_fust_g.t1   = rstmif.status.idx[m_rs1].tag;
      diif.n_fust_g.t2   = rstmif.status.idx[m_rs2].tag;
      diif.n_fust_g.t3   = rstmif.status.idx[m_rs3].tag;
    end

    always_comb begin : Dispatch_Out
      dispatch = diif.out;

      // To Execute
      dispatch.fu_s = cuif.fu_s;
      dispatch.fu_m = cuif.fu_m;

      dispatch.ex_ctr.imm = cuif.imm;
      dispatch.ex_ctr.alu_op = cuif.alu_op;
      dispatch.ex_ctr.branch_op = cuif.branch_op;
      dispatch.ex_ctr.s_mem_type = cuif.s_mem_type;
      dispatch.ex_ctr.m_mem_type = cuif.m_mem_type;
      dispatch.ex_ctr.m_rw = cuif.matrix_rd;
      dispatch.ex_ctr.m_rw_en = cuif.m_reg_write;

      // To Writeback
      dispatch.wb_ctr.s_rw_en = cuif.s_reg_write;
      dispatch.wb_ctr.s_rw = s_rd;
    end

    function automatic void init_rst();
      begin
        rstsif.di_sel = '0;
        rstsif.di_write = 1'b0;
        rstsif.di_tag = '0;
        rstsif.wb_sel = '0;
        rstsif.wb_write = 1'b0;

        rstmif.di_sel = '0;
        rstmif.di_write = 1'b0;
        rstmif.di_tag = '0;
        rstmif.wb_sel = '0;
        rstmif.wb_write = 1'b0;
      end
    endfunction
endmodule
