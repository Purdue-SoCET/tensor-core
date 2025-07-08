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
    regbits_t s_rd, s_rs1, s_rs2, m_stride;
    matbits_t m_rd, m_rs1, m_rs2, m_rs3;
    logic flush;
    dispatch_t n_dispatch;
    dispatch_t dispatch;
    matbits_t gemm_weight_addr;
    logic spec;
    logic n_spec;
    logic jump;
    logic n_jump;
    word_t fetch_br_pc;
    logic fetch_br_pred;
    logic n_halt, halt;
    logic n_new_weight, new_weight;
    fust_s_row_t [2:0] out_op;

    // n_dispatch is combinationally set by output logic
    always_ff @ (posedge CLK, negedge nRST) begin: Pipeline_Latching
      if (~nRST)
        diif.out <= '0;
    	else
        diif.out <= n_dispatch;
    end

    assign out_op[0] = diif.fust_s_out_op_alu;
    assign out_op[1] = diif.fust_s_out_op_sls;
    assign out_op[2] = diif.fust_s_out_op_br;

    // current pc and branch prediction (taken = 1 or not taken = 0) from fetch
    always_comb begin
      fetch_br_pc  = diif.out.n_br_pc;
      fetch_br_pred = diif.out.n_br_pred;
      if (cuif.fu_s == FU_S_BRANCH) begin
        fetch_br_pc  = diif.fetch.br_pc;
        fetch_br_pred = diif.fetch.br_pred;
      end
    end

    // if there are new new weights for the systollic array, scratchpad needs to load in new weight matrix
    // if no change in weights from previous gemm instr, scratchpad can directly load in input and partial sum matrices
    always_comb begin
      gemm_weight_addr = diif.fust_g.op.ms2;
      n_new_weight = new_weight;
      if (cuif.fu_m == FU_M_GEMM) begin
        gemm_weight_addr = m_rs2;
        n_new_weight = 1'b0;
      end
      else if (cuif.m_mem_type == M_LOAD) begin
        if (diif.fust_g.op.ms2 == m_rd) begin
          n_new_weight = 1'b1;
        end
      end
    end

    always_ff @(posedge CLK, negedge nRST) begin
      if (!nRST) begin
        new_weight = '0;
      end
      else begin 
        new_weight = n_new_weight;
      end
    end

    // when there is a branch miss, fust and certain latches need to be flushed
    assign flush = diif.branch_miss;

    // n_dispatch is set based on what is happening
    // if flush (branch miss), decoded instruction is cleared
    // if there is a hazard (logic below), output should be held until hazars cleared
    always_comb begin : Pipeline_Output
      case (1'b1)
        flush:       n_dispatch = '0;
        hazard:      n_dispatch = diif.out;
        default:     n_dispatch = dispatch; 
      endcase
    end

    // decoding registers bsaed on instruction
    // depending on type of instr, registers not being used are set to 0 for clean dependence checking 
    always_comb begin: Instr_Signals
      instr  = diif.fetch.imemload;
      s_rd   = (cuif.s_mem_type == STORE || (cuif.fu_s == FU_S_BRANCH && !(cuif.jal || cuif.jalr)) ) ? '0 : instr[11:7];
      s_rs1  = (cuif.u_type == UT_LOAD || cuif.jal) ? '0 : (cuif.fu_m == FU_M_LD_ST) ? instr [25:21] : instr[19:15];
      s_rs2  = (cuif.i_flag || cuif.jal || (cuif.u_type == UT_LOAD)) ? '0 : instr[24:20];
      m_rd   = instr[31:26];
      m_rs1  = instr[25:20];
      m_rs2  = instr[19:14];
      m_rs3  = instr[13:8];
    end

    // control unit takes in instruction passed from fetch
    always_comb begin : Control_Unit
      cuif.instr = instr;
    end

    
    always_comb begin : Hazard_Logic
      // hazard logic to check if there is a structural hazard
      case (cuif.fu_s)
        FU_S_ALU:     s_busy = (diif.fu_ex[0] == 1'b0 || (|diif.fust_s_out_t1 || |diif.fust_s_out_t2)) ? (diif.fu_ex[0] == 1'b1) ? '0 : diif.fust_s_out_busy[FU_S_ALU] : '0;
        FU_S_LD_ST:   s_busy = (diif.fu_ex[1] == 1'b0 || (|diif.fust_s_out_t1 || |diif.fust_s_out_t2)) ? (diif.fu_ex[1] == 1'b1) ? '0 : diif.fust_s_out_busy[FU_S_LD_ST] : '0;
        FU_S_BRANCH:  s_busy = (diif.fu_ex[2] == 1'b0 || (|diif.fust_s_out_t1 || |diif.fust_s_out_t2)) ? (diif.fu_ex[2] == 1'b1) ? '0 : diif.fust_s_out_busy[FU_S_BRANCH] : '0;
        default: s_busy = 1'b0;
      endcase
      case (cuif.fu_m)
        FU_M_LD_ST:   m_busy = (diif.fu_ex[3] == 1'b0) || (|diif.fust_m.t1 || |diif.fust_m.t2) ? (diif.fu_ex[3] == 1'b1) ? '0 : diif.fust_m.busy : '0;
        FU_M_GEMM:    m_busy = (diif.fu_ex[4] == 1'b0) ? diif.fust_g.busy : '0;
        default: m_busy = 1'b0;
      endcase

      // hazard logic if there is a waw hazard
      WAW = (cuif.m_mem_type == M_LOAD || cuif.fu_m == FU_M_GEMM) ? rstmif.status.idx[m_rd].busy : 
            (cuif.s_reg_write || (cuif.jal || cuif.jalr)) ? rstsif.status.idx[s_rd].busy: 1'b0;
      hazard = (s_busy | m_busy | WAW); 
    end

    // if there is a branch, instructions following are in "speculation state"
    always_comb begin : Speculation_State
      n_spec = spec;
      if (diif.branch_resolved || diif.branch_miss)
        n_spec = 1'b0;
      else if (cuif.fu_s == FU_S_BRANCH && !(cuif.jal || cuif.jalr))
        n_spec = 1'b1;
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Speculation_State_Latch
      if (~nRST)
        spec <= '0;
      else
        spec <= n_spec;
    end

    // if there is a jump, no new instructions come until fetch brings in the pc resulting from the jump
    // ex. 
    // at pc 100, jump instr to pc 124
    // fetch holds pc and instr signals to 0 until it gets instr for pc 124
    always_comb begin : Jump_State
      n_jump = jump;
      if ((diif.branch_resolved && !(cuif.jal || cuif.jalr)) || diif.branch_miss)
        n_jump = 1'b0;
      else if (cuif.jal || cuif.jalr)
        n_jump = 1'b1;
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Jump_State_Latch
      if (~nRST)
        jump <= '0;
      else
        jump <= n_jump;
    end

    // if halt, halt latch is set and cleared if there is a branch miss meaning that halt came after a mispredicted branch
    // fetch holds pc and instr signal to 0 when diif.halt is high, if cleared, fetch will bring whatever resolved pc's instr
    assign n_halt = (diif.branch_miss) ? '0 : (halt || cuif.halt);
    assign diif.halt = (halt || n_halt);
    
    always_ff @(posedge CLK, negedge nRST) begin : Halt_Latch
      if (!nRST) begin
        halt <= '0;
      end
      else begin 
        halt <= n_halt;
      end
    end

    always_comb begin : Reg_Status_Tables
      init_rst(); 

      // reg status tables (rsts) are set whenever there is an instruction writing to a register
      // when set, the status table holds what functional unit will be writing to it
      // ex.
      // if alu is writing to reg 5, reg 5 in scalar rsts will be set to 1
      // if matrix lead to matrix reg 10, matrix reg 10 in matrix rsts will be set to 2

      // there is a rsts for scalar and for matrix - scalar same size as reg file (32), matrix same as scratchpad (64)

      // rsts also hold spec bit, when branch miss, the whole status is cleared as it will not be written to
      // if branch resolved (correct prediction), only spec bit is cleared
      rstsif.di_write = 1'b0;
      rstsif.spec = 1'b0;
      rstsif.flush = diif.branch_miss;
      rstsif.resolved = diif.branch_resolved;
      if (cuif.s_reg_write || (cuif.jal || cuif.jalr)) begin
        if (~hazard & ~flush) begin 
          rstsif.di_sel = s_rd;
          rstsif.di_write = 1'b1;
          rstsif.di_tag = (cuif.fu_s == FU_S_LD_ST) ? 2'd3 : (cuif.fu_s == FU_S_ALU) ? 2'd1 : 2'd2; // 1 for ALU, 3 for LD, 2 for BR (jump)
          rstsif.spec = spec;
        end
      end

      if (cuif.m_reg_write) begin
        if (~hazard & ~flush) begin
          rstmif.di_sel = m_rd;
          rstmif.di_write = 1'b1;
          rstmif.di_tag = (cuif.fu_m == FU_M_LD_ST) ? 2'd2 : 2'd1; // 1 for GEMM, 2 for LD
        end
      end


      // clearing reg status tables when data written to reg file or scratchpad done
      if (diif.wb.s_rw_en) begin 
        rstsif.wb_sel = diif.wb.s_rw;
        rstsif.wb_write = '1;
      end

      if (diif.wb.gemm_done) begin 
        rstmif.wb_sel = diif.fust_g.op.md;
        rstmif.wb_write = '1;
      end

      if (diif.wb.m_load_done) begin 
        rstmif.wb_sel = diif.fust_m.op.md;
        rstmif.wb_write = '1;
      end
    end

    // next logic for functional unit status tables (fusts), these are sent to issue where the fusts get written to
    // fust for the three types of instructions
    // 1. scalar - branch/jump fu, alu fu, scalar ld/st fu
    // 2. matrix - matrix ld/st fu
    // 3. gemm   - gemm fu
    always_comb begin : FUST
      diif.n_fu_t = cuif.fu_t;
      diif.n_t1 = diif.fust_s_out_t1;
      diif.n_t2 = diif.fust_s_out_t2;
      diif.n_s_t1 = diif.fust_m.t1;

      // t1 and t2 are scalar tags - cleared whenever the regs are written to - notified by writeback stage
      // s_t1 is scalar tag for matrix load and store - used for calculating memory location - cleared same way as scalar instrunction tags t1 and t2
      if (diif.wb.s_rw_en && diif.wb.alu_done) begin
        diif.n_t1[FU_S_LD_ST] = ((diif.wb.s_rw == out_op[FU_S_LD_ST].rs1) && (diif.fust_s_out_t1[FU_S_LD_ST] == 2'd1) && diif.fust_s_out_busy[FU_S_LD_ST]) ? '0 : diif.fust_s_out_t1[FU_S_LD_ST];
        diif.n_t2[FU_S_LD_ST] = ((diif.wb.s_rw == out_op[FU_S_LD_ST].rs2) && (diif.fust_s_out_t2[FU_S_LD_ST] == 2'd1) && diif.fust_s_out_busy[FU_S_LD_ST]) ? '0 : diif.fust_s_out_t2[FU_S_LD_ST];
        diif.n_t1[FU_S_BRANCH] = ((diif.wb.s_rw == out_op[FU_S_BRANCH].rs1) && (diif.fust_s_out_t1[FU_S_BRANCH] == 2'd1) && diif.fust_s_out_busy[FU_S_BRANCH]) ? '0 : diif.fust_s_out_t1[FU_S_BRANCH];
        diif.n_t2[FU_S_BRANCH] = ((diif.wb.s_rw == out_op[FU_S_BRANCH].rs2) && (diif.fust_s_out_t2[FU_S_BRANCH] == 2'd1) && diif.fust_s_out_busy[FU_S_BRANCH]) ? '0 : diif.fust_s_out_t2[FU_S_BRANCH];
        diif.n_t1[FU_S_ALU] = ((diif.wb.s_rw == out_op[FU_S_ALU].rs1) && (diif.fust_s_out_t1[FU_S_ALU] == 2'd1) && diif.fust_s_out_busy[FU_S_ALU]) ? '0 : diif.fust_s_out_t1[FU_S_ALU];
        diif.n_t2[FU_S_ALU] = ((diif.wb.s_rw == out_op[FU_S_ALU].rs2) && (diif.fust_s_out_t2[FU_S_ALU] == 2'd1) && diif.fust_s_out_busy[FU_S_ALU]) ? '0 : diif.fust_s_out_t2[FU_S_ALU];
        diif.n_s_t1 = (diif.fust_m.t1 == 2'd1 && diif.fust_m.busy) ? '0 : diif.fust_m.t1;
      end else if (diif.wb.s_rw_en && diif.wb.jump_done) begin
        diif.n_t1[FU_S_ALU] = (diif.wb.s_rw == out_op[FU_S_ALU].rs1) && (diif.fust_s_out_t1[FU_S_ALU] == 2'd2) && diif.fust_s_out_busy[FU_S_ALU] ? '0 : diif.fust_s_out_t1[FU_S_ALU];
        diif.n_t2[FU_S_ALU] = (diif.wb.s_rw == out_op[FU_S_ALU].rs2) && (diif.fust_s_out_t2[FU_S_ALU] == 2'd2) && diif.fust_s_out_busy[FU_S_ALU] ? '0 : diif.fust_s_out_t2[FU_S_ALU];
        diif.n_t1[FU_S_BRANCH] = (diif.wb.s_rw == out_op[FU_S_BRANCH].rs1) && (diif.fust_s_out_t1[FU_S_BRANCH] == 2'd2) && diif.fust_s_out_busy[FU_S_BRANCH] ? '0 : diif.fust_s_out_t1[FU_S_BRANCH];
        diif.n_t2[FU_S_BRANCH] = (diif.wb.s_rw == out_op[FU_S_BRANCH].rs2) && (diif.fust_s_out_t2[FU_S_BRANCH] == 2'd2) && diif.fust_s_out_busy[FU_S_BRANCH] ? '0 : diif.fust_s_out_t2[FU_S_BRANCH];
        diif.n_t1[FU_S_LD_ST] = (diif.wb.s_rw == out_op[FU_S_LD_ST].rs1) && (diif.fust_s_out_t1[FU_S_LD_ST] == 2'd2) && diif.fust_s_out_busy[FU_S_LD_ST] ? '0 : diif.fust_s_out_t1[FU_S_LD_ST];
        diif.n_t2[FU_S_LD_ST] = (diif.wb.s_rw == out_op[FU_S_LD_ST].rs2) && (diif.fust_s_out_t2[FU_S_LD_ST] == 2'd2) && diif.fust_s_out_busy[FU_S_LD_ST] ? '0 : diif.fust_s_out_t2[FU_S_LD_ST];
        diif.n_s_t1 = (diif.fust_m.t1 == 2'd2 && diif.fust_m.busy) ? '0 : diif.fust_m.t1;
      end else if (diif.wb.s_rw_en && diif.wb.load_done) begin
        diif.n_t1[FU_S_ALU] = (diif.wb.s_rw == out_op[FU_S_ALU].rs1) && (diif.fust_s_out_t1[FU_S_ALU] == 2'd3) && diif.fust_s_out_busy[FU_S_ALU] ? '0 : diif.fust_s_out_t1[FU_S_ALU];
        diif.n_t2[FU_S_ALU] = (diif.wb.s_rw == out_op[FU_S_ALU].rs2) && (diif.fust_s_out_t2[FU_S_ALU] == 2'd3) && diif.fust_s_out_busy[FU_S_ALU] ? '0 : diif.fust_s_out_t2[FU_S_ALU];
        diif.n_t1[FU_S_LD_ST] = (diif.wb.s_rw == out_op[FU_S_LD_ST].rs1) && (diif.fust_s_out_t1[FU_S_LD_ST] == 2'd3) && diif.fust_s_out_busy[FU_S_LD_ST] ? '0 : diif.fust_s_out_t1[FU_S_LD_ST];
        diif.n_t2[FU_S_LD_ST] = (diif.wb.s_rw == out_op[FU_S_LD_ST].rs2) && (diif.fust_s_out_t2[FU_S_LD_ST] == 2'd3) && diif.fust_s_out_busy[FU_S_LD_ST] ? '0 : diif.fust_s_out_t2[FU_S_LD_ST];
        diif.n_t1[FU_S_BRANCH] = (diif.wb.s_rw == out_op[FU_S_BRANCH].rs1) && (diif.fust_s_out_t1[FU_S_BRANCH] == 2'd3) && diif.fust_s_out_busy[FU_S_BRANCH] ? '0 : diif.fust_s_out_t1[FU_S_BRANCH];
        diif.n_t2[FU_S_BRANCH] = (diif.wb.s_rw == out_op[FU_S_BRANCH].rs2) && (diif.fust_s_out_t2[FU_S_BRANCH] == 2'd3) && diif.fust_s_out_busy[FU_S_BRANCH] ? '0 : diif.fust_s_out_t2[FU_S_BRANCH];
        diif.n_s_t1 = (diif.fust_m.t1 == 2'd3 && diif.fust_m.busy) ? '0 : diif.fust_m.t1;
      end
      
      // setting scalar tags t1 and t2 looking at reg status tables to see what functional unit is writing to that register
      if (!(diif.wb.s_rw_en && (diif.wb.s_rw == s_rs1)) && !hazard) begin
        diif.n_t1[cuif.fu_s] = rstsif.status.idx[s_rs1].tag;
      end
      if (!(diif.wb.s_rw_en && (diif.wb.s_rw == s_rs2)) && !hazard) begin
        diif.n_t2[cuif.fu_s] = rstsif.status.idx[s_rs2].tag;
      end

      // gt1, gt2, and gt3 are matrix tags for gemm instructions - cleared whenever matrix load finishes 
      // none of the tags are needed to be cleared when gemm isntr happens because that is a structural hazard and
      // gemm done signal is set by scratchpad when systollic array has written output matrix
      if (diif.wb.m_load_done) begin
        diif.n_gt1 = (diif.fust_g.t1 != '0) && diif.fust_g.busy ? '0 : diif.fust_g.t1;
        diif.n_gt2 = (diif.fust_g.t2 != '0) && diif.fust_g.busy ? '0 : diif.fust_g.t2;
        diif.n_gt3 = (diif.fust_g.t3 != '0) && diif.fust_g.busy ? '0 : diif.fust_g.t3;
      end
      else begin
        diif.n_gt1 = (cuif.fu_t == FU_G_T & ~flush & ~hazard) ? rstmif.status.idx[m_rs1].tag : diif.fust_g.t1;
        diif.n_gt2 = (cuif.fu_t == FU_G_T & ~flush & ~hazard) ? rstmif.status.idx[m_rs2].tag : diif.fust_g.t2;
        diif.n_gt3 = (cuif.fu_t == FU_G_T & ~flush & ~hazard) ? rstmif.status.idx[m_rs3].tag : diif.fust_g.t3;
      end

      // m_t2 is matrix tag for matrix stores and loads - cleared when gemm instr is done
      // no need to explicitely clear on matrix load or store done as it is a structural hazard and scratchpad
      // only says done signal whenever matrix is finished storing or loading to or from memory
      if (diif.wb.gemm_done)  begin
        diif.n_m_t2 = (diif.fust_m.t2 != '0) && diif.fust_m.busy ? '0 : diif.fust_m.t2;
      end
      else begin // setting tag
        diif.n_m_t2  = (cuif.fu_t == FU_M_T & ~flush & ~hazard) ? rstmif.status.idx[m_rd].tag  : diif.fust_m.t2;
      end

      // setting tag
      if (!(diif.wb.s_rw_en && (diif.wb.s_rw == s_rs1)) && !hazard)begin
        diif.n_s_t1 = rstsif.status.idx[s_rs1].tag;
      end


      // To Issue **Combinationally** (is latched when into fust in issue) - fusts also hold necessary control signals and data
      
      // scalar
      diif.n_fust_s_en     = (cuif.fu_t == FU_S_T & ~flush & ~hazard);
      diif.n_fu_s          = cuif.fu_s;
      diif.n_fust_s.rd     = s_rd;
      diif.n_fust_s.rs1    = s_rs1;
      diif.n_fust_s.rs2    = s_rs2;
      diif.n_fust_s.imm    = cuif.imm;
      diif.n_fust_s.i_type = cuif.i_flag;
      diif.n_fust_s.lui    = (cuif.u_type == UT_LOAD);
      diif.n_fust_s.j_type = (cuif.jal) ? 2'd1 : (cuif.jalr) ? 2'd2 : 2'd0;
      diif.n_fust_s.spec   = spec && !(diif.branch_resolved || diif.branch_miss); // sets spec bit in FUST on new instructions
      diif.n_fust_s.op_type = '0;
      diif.n_fust_s.mem_type = scalar_mem_t'('0);

      if (cuif.fu_s == FU_S_ALU) begin
        diif.n_fust_s.op_type = cuif.alu_op;
      end 
      else if (cuif.fu_s == FU_S_BRANCH) begin
        diif.n_fust_s.op_type = {1'b0,cuif.branch_op};
      end

      if (cuif.fu_s == FU_S_LD_ST) begin
        diif.n_fust_s.mem_type = cuif.s_mem_type;
      end

      // matrix ld/st
      diif.n_fust_m.mem_type = matrix_mem_t'('0);
      diif.n_fust_m.spec = spec && !(diif.branch_resolved || diif.branch_miss);

      if (cuif.fu_m == FU_M_LD_ST) begin
        diif.n_fust_m.mem_type = cuif.m_mem_type;
      end

      diif.n_fust_m_en   = (cuif.fu_t == FU_M_T & ~flush & ~hazard);
      diif.n_fust_m.md   = m_rd;
      diif.n_fust_m.rs1  = s_rs1;
      diif.n_fust_m.imm  = cuif.imm;

      // gemm
      diif.n_fust_g_en   = (cuif.fu_t == FU_G_T & ~flush & ~hazard);
      diif.n_fust_g.md   = m_rd;
      diif.n_fust_g.ms1  = m_rs1;
      diif.n_fust_g.ms2  = m_rs2;
      diif.n_fust_g.ms3  = m_rs3;
      diif.n_fust_g.spec = spec && !(diif.branch_resolved || diif.branch_miss);

      diif.n_fust_g.new_weight = ((diif.fust_g.op.ms2 != m_rs2) || new_weight);
    end

    // output logic
    always_comb begin : Dispatch_Out 
      dispatch = diif.out;

      // To Execute
      dispatch.fu_s = cuif.fu_s;
      dispatch.fu_m = cuif.fu_m;

      // halt
      dispatch.halt = cuif.halt;

      // spec
      dispatch.spec = spec;

      // To Fetch
      diif.freeze = hazard;
      dispatch.freeze = hazard;
      diif.jump = (n_jump || jump) && !(diif.fu_ex[2] == 1'b1);

      // Scratchpad Weight Addr
      dispatch.gemm_weight_addr = gemm_weight_addr;

      // Branch 
      dispatch.n_br_pc = fetch_br_pc;
      dispatch.n_br_pred = fetch_br_pred;

    end

    // initializations for reg status tables, no particular reason it was done as a function
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
