// fust gets written to in dispatch on clock edge
// issue should read registers and issue to execute by the next clock edge
`include "datapath_types.vh"
`include "issue_if.vh"
`include "regfile.sv"
`include "regfile_if.vh"
`include "fust_s.sv"
`include "fust_s_if.vh"
`include "fust_m.sv"
`include "fust_m_if.vh"
`include "fust_g.sv"
`include "fust_g_if.vh"

module issue(
    input logic CLK, nRST,
    issue_if.IS isif
);

    import isa_pkg::*;
    import datapath_pkg::*;

    // Instantiations
    regfile_if rfif();
    fust_s_if fusif();
    fust_m_if fumif();
    fust_g_if fugif();

    regfile RF (CLK, nRST, rfif);
    fust_s FS (CLK, nRST, fusif);
    fust_m FM (CLK, nRST, fumif);
    fust_g FG (CLK, nRST, fugif);

    logic hazard, halt;
    fust_s_t fust_s;
    fust_m_t fust_m;
    fust_g_t fust_g;
    issue_t n_issue;
    issue_t issue;
    regbits_t s_rs1, s_rs2;
    word_t imm;
    logic [4:0] incoming_instr;
    logic [4:0] fu_ready, next_ready;
    logic single_ready, next_single_ready;
    logic [4:0] rdy;
    logic [4:0] n_rdy;
    logic [4:0][5:0] age;
    logic [4:0][5:0] n_age;
    fust_state_e [4:0] fust_state;
    fust_state_e [4:0] next_fust_state;
    logic [4:0] oldest_rdy;
    logic [4:0] next_oldest_rdy;
    logic i_type;
    logic lui_type;
    logic n_halt;

    // incoming_instr signal holds what fu is needed by that instr
    always_comb begin : Incoming_Instr_Logic
      incoming_instr = '0;
      if (!isif.dispatch.freeze) begin
        if (isif.n_fu_t == FU_S_T) begin
          case (isif.n_fu_s)
            FU_S_ALU:    incoming_instr = 5'b00001;
            FU_S_LD_ST:  incoming_instr = 5'b00010;
            FU_S_BRANCH: incoming_instr = 5'b00100;
            default: incoming_instr = '0;
          endcase
        end else if (isif.n_fu_t == FU_M_T)
          incoming_instr = 5'b01000;
        else if (isif.n_fu_t == FU_G_T)
          incoming_instr = 5'b10000;
      end
    end
      
    // n_issue is combinationally set by output logic
    always_ff @ (posedge CLK, negedge nRST) begin: Pipeline_Latching
      if (~nRST)
        isif.out <= '0;
    	else
        isif.out <= n_issue;
    end
    
    // if hazard set from dispatch, output stays the same
    always_comb begin : Pipeline_Output
      case (1'b1)
        isif.dispatch.freeze: n_issue = isif.out; 
        default:     n_issue = issue;
      endcase
    end

    // control inputs to register file
    always_comb begin : Regfile
      rfif.WEN   = isif.wb.reg_en;
      rfif.wsel  = isif.wb.reg_sel;
      rfif.wdata = isif.wb.wdat;
      rfif.rsel1 = s_rs1;
      rfif.rsel2 = s_rs2;
    end

    // writing the fust logic from dispatch combinationally - key area for speed up but possible loss in cycles
    always_comb begin : FUST
      // scalar
      fusif.en       = isif.n_fust_s_en;
      fusif.fu       = isif.n_fu_s;
      fusif.fust_row = isif.n_fust_s; 
      fusif.resolved = isif.branch_resolved;

      // states say what functional units are being used
      fusif.busy[0]  = (fust_state[0] == FUST_EX && (next_fust_state[0] == FUST_EMPTY || (next_fust_state[0] == FUST_WAIT && !incoming_instr[0]))) ? 1'd0 : next_fust_state[0] != FUST_EMPTY;
      fusif.busy[1]  = (fust_state[1] == FUST_EX && (next_fust_state[1] == FUST_EMPTY || next_fust_state[1] == FUST_WAIT)) ? 1'd0 : next_fust_state[1] != FUST_EMPTY;
      fusif.busy[2]  = (fust_state[2] == FUST_EX && (next_fust_state[2] == FUST_EMPTY || next_fust_state[2] == FUST_WAIT)) ? 1'd0 : next_fust_state[2] != FUST_EMPTY;

      fusif.t1 = isif.n_t1;
      fusif.t2 = isif.n_t2;

      fusif.flush = isif.branch_miss;

      // matrix
      fumif.en       = isif.n_fust_m_en;
      fumif.fust_row = isif.n_fust_m;
      fumif.busy     = (fust_state[3] == FUST_EX && (next_fust_state[3] == FUST_EMPTY || next_fust_state[3] == FUST_WAIT)) ? 1'd0 : next_fust_state[3] != FUST_EMPTY;

      fumif.t1 = isif.n_s_t1; // t1 is for scalar reg
      fumif.t2 = isif.n_m_t2; // t2 is for matrix reg

      fumif.flush = isif.branch_miss;
      fumif.resolved = isif.branch_resolved;

      // gemm
      fugif.en       = isif.n_fust_g_en;
      fugif.fust_row = isif.n_fust_g;
      fugif.busy     = (fust_state[4] == FUST_EX && (next_fust_state[4] == FUST_EMPTY || next_fust_state[4] == FUST_WAIT)) ? 1'd0 : next_fust_state[4] != FUST_EMPTY;

      fugif.t1 = isif.n_gt1;
      fugif.t2 = isif.n_gt2;
      fugif.t3 = isif.n_gt3;

      fugif.flush = isif.branch_miss;
      fugif.resolved = isif.branch_resolved;

    end

    // age logic for knowing what instr is the oldest to issue - insreased by 1 whenever new instr comes into issue
    always_comb begin : Age_Logic
      n_age = age;
      for (int i = 0; i < 5; i++) begin
        case (fust_state[i])
          FUST_EMPTY: n_age[i] = {1'b0,incoming_instr[i]}; // set new instructions to age 1
          FUST_WAIT:  n_age[i] = (next_fust_state[i] == FUST_EX) ? 1'b0 : (|incoming_instr) ? age[i] + 1 : age[i];
          FUST_RDY:   n_age[i] = (next_fust_state[i] == FUST_EX) ? 1'b0 : (|incoming_instr) ? age[i] + 1 : age[i];
          FUST_EX:    n_age[i] = (next_fust_state[i] == FUST_WAIT) ? 1'b1 :'0;
          default: n_age = age;
        endcase
      end
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Age_Latch
      if (~nRST)
        age <= '0;
      else
        age <= n_age;
    end
    
    // oldest_rdy signal is for knowing which signal has been ready the longest looking at age and if ready
    always_comb begin : Oldest_Logic
      next_oldest_rdy = oldest_rdy;
      next_oldest_rdy[0] = (rdy[0] && (age[0] > age[1]) && (age[0] > age[2]) && (age[0] > age[3]) && (age[0] > age[4])) ? 1'b1 : (next_fust_state[0] == FUST_EMPTY || (fust_state[0] == FUST_EX && next_fust_state[0] == FUST_WAIT)) ? 1'b0 : oldest_rdy[0];
      next_oldest_rdy[1] = (rdy[1] && (age[1] > age[0]) && (age[1] > age[2]) && (age[1] > age[3]) && (age[1] > age[4])) ? 1'b1 : (next_fust_state[1] == FUST_EMPTY || (fust_state[1] == FUST_EX && next_fust_state[1] == FUST_WAIT)) ? 1'b0 : oldest_rdy[1];
      next_oldest_rdy[2] = (rdy[2] && (age[2] > age[0]) && (age[2] > age[1]) && (age[2] > age[3]) && (age[2] > age[4])) ? 1'b1 : (next_fust_state[2] == FUST_EMPTY || (fust_state[2] == FUST_EX && next_fust_state[2] == FUST_WAIT)) ? 1'b0 : oldest_rdy[2];
      next_oldest_rdy[3] = (rdy[3] && (age[3] > age[0]) && (age[3] > age[1]) && (age[3] > age[2]) && (age[3] > age[4])) ? 1'b1 : (next_fust_state[3] == FUST_EMPTY || (fust_state[3] == FUST_EX && next_fust_state[3] == FUST_WAIT)) ? 1'b0 : oldest_rdy[3];
      next_oldest_rdy[4] = (rdy[4] && (age[4] > age[0]) && (age[4] > age[1]) && (age[4] > age[2]) && (age[4] > age[3])) ? 1'b1 : (next_fust_state[4] == FUST_EMPTY || (fust_state[4] == FUST_EX && next_fust_state[4] == FUST_WAIT)) ? 1'b0 : oldest_rdy[4];
    
      // cleared when fu goes to being empty
      for (int i = 0; i < 5; i++) begin
        if (next_fust_state[i] == FUST_EMPTY) begin
          next_oldest_rdy[i] = '0;
        end
      end
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Oldest_Latch
      if (~nRST) begin
        oldest_rdy <= '0;
      end else begin
        oldest_rdy <= next_oldest_rdy;
      end
    end

    // rdy signal set when there are no dependencies
    always_comb begin : Ready_Logic
      n_rdy = rdy;
      for (int i = 0; i < 5; i++) begin
        case (fust_state[i])
          FUST_EMPTY: n_rdy[i] = 1'b0;
          FUST_WAIT: begin // implies instruction is already loaded
            if (i < 3) begin // Scalar FUST
              n_rdy[i] = (!(|fusif.fust.t1[i]) && !(|fusif.fust.t2[i]));
            end else if (i == 3) begin // Matrix LD/ST FUST
              n_rdy[i] = (!(|fumif.fust.t1) && !(|fumif.fust.t2));
            end else if (i == 4) begin // GEMM FUST
              n_rdy[i] = (!(|fugif.fust.t1) && !(|fugif.fust.t2) && !(|fugif.fust.t3));
            end
          end
          FUST_EX: n_rdy[i] = 1'b0;
          default: n_rdy[i] = rdy[i];
        endcase
      end
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Ready_Latch
      if (~nRST)
        rdy <= '0;
      else
        rdy <= n_rdy;
    end

    // whenever there is more than one instruction that becomes ready at the same time, logic to handle that, oldest one gets selected
    // only one instr issued at a time
    always_comb begin
      fu_ready = '0;
      next_ready = '0;
      for (int i = 0; i < 5; i++) begin 
        if (fust_state[i] == FUST_RDY) begin
          fu_ready[i] = 1'b1;
        end
        if (n_rdy[i]) begin
          next_ready[i] = 1'b1;
        end
      end
      single_ready = (fu_ready == 5'd1) || (fu_ready == 5'd2) || (fu_ready == 5'd4) || (fu_ready == 5'd8) || (fu_ready == 5'd16);
      next_single_ready = (next_ready == 5'd1) || (next_ready == 5'd2) || (next_ready == 5'd4) || (next_ready == 5'd8) || (next_ready == 5'd16);
    end

    // states for each funtional unit:
    // FUST_EMPTY - empty and waiting for an instr
    // FUST_WAIT  - instr has been put into the fusts and check dependencies here
    // FUST_RDY   - dependencies cleared and waiting for functional unit to be clear
    // FUST_EX    - instr is in functional unit in execute stage
    // instr can go straight from wait to ex if no dependencies or hazards
    always_ff @ (posedge CLK, negedge nRST) begin: FUST_State
      if (~nRST)
        fust_state <= {5{FUST_EMPTY}};
    	else
        fust_state <= next_fust_state;
    end

    // Issue Policy: Oldest instruction first
    always_comb begin : FUST_Next_State
      next_fust_state = fust_state;
        for (int i = 0; i < 5; i++) begin
          if (isif.branch_miss) begin
            next_fust_state[2] = FUST_EMPTY;
            if ((i < 3) && fusif.fust.op[i].spec) begin
              next_fust_state[i] = FUST_EMPTY;
            end
            else if ((i == 3) && fumif.fust.op.spec) begin
              next_fust_state[i] = FUST_EMPTY;
            end
            else if ((i == 4) && fugif.fust.op.spec) begin
              next_fust_state[i] = FUST_EMPTY;
            end
          end
          else begin
            case (fust_state[i])
              FUST_EMPTY: begin
                next_fust_state[i] = (incoming_instr[i]) ? FUST_WAIT : FUST_EMPTY;
              end
              FUST_WAIT: begin
                if (n_rdy[i]) begin
                  if ((i==3 || i==4 || i==1) && fusif.fust.op[i].spec) begin
                    next_fust_state[i] = FUST_RDY;
                  end 
                  else begin
                    next_fust_state[i] = (((n_rdy[i] == next_oldest_rdy[i]) || (next_single_ready && next_ready[i]))) ? FUST_EX : FUST_RDY;
                  end
                end
              end
              FUST_RDY: begin
                if ((i==3 || i==4 || i==1) && fusif.fust.op[i].spec) begin 
                    next_fust_state[i] = FUST_RDY;
                end 
                else begin 
                  next_fust_state[i] = (((next_oldest_rdy[i]) || (single_ready && fu_ready[i]))) ? FUST_EX : FUST_RDY;
                end
              end
              FUST_EX: begin
                if ((isif.fu_ex[0] == 1'b1) && (i == 0)) begin 
                  next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
                end
                else if ((isif.fu_ex[1] == 1'b1) && (i == 1)) begin
                  next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
                end
                else if ((isif.fu_ex[2] == 1'b1) && (i == 2)) begin
                  next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
                end
                else if ((isif.fu_ex[3] == 1'b1) && (i == 3)) begin
                  next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
                end
                else if ((isif.fu_ex[4] == 1'b1) && (i == 4)) begin
                  next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
                end  
              end
              default: begin
                next_fust_state = fust_state;
              end
            endcase
          end
        end
    end

    // halt logic - same as dispatch
    assign n_halt = (isif.branch_miss) ? '0 : (halt || isif.dispatch.halt);
    assign isif.halt = halt;

    always_ff @(posedge CLK, negedge nRST) begin : Halt_Latch
      if (!nRST) begin
        halt <= '0;
      end
      else begin 
        halt <= n_halt;
      end
    end

    // when the next state for an instr is changing to FUST_EX, the output control signals and data are outputted here
    always_comb begin : Output_Logic
      issue = isif.out;
      isif.fust_state = fust_state;
      s_rs1 = '0;
      s_rs2 = '0;
      imm = '0;
      i_type = '0;
      lui_type = '0;
      issue.halt = '0;
      // halt is only set when all instructions that come before are done and there is no branch miss
      if (!(|isif.fust_s.busy || isif.fust_m.busy || isif.fust_g.busy || isif.branch_miss)) begin
        issue.halt = halt;
      end
      for (int i = 0; i < 5; i++) begin
        if (isif.fu_ex[i]) begin
          issue.fu_en[i] = 1'b0;
        end
        if (fust_state[i] != FUST_EX && next_fust_state[i] == FUST_EX) begin // state going from either wait or rdy to ex
          if (i < 3) begin // scakar alu, scalar ld/st, br
            s_rs1 = fusif.fust.op[i].rs1;
            s_rs2 = fusif.fust.op[i].rs2;
            i_type = fusif.fust.op[i].i_type;
            lui_type = fusif.fust.op[i].lui;
            issue.fu_en[i] = 1'b1;
            imm = fusif.fust.op[i].imm;
            issue.alu_op = aluop_t'(fusif.fust.op[i].op_type);
            issue.mem_type = scalar_mem_t'(fusif.fust.op[i].mem_type);
            issue.branch_type = branch_t'(fusif.fust.op[i].op_type);
            issue.branch_pc = isif.dispatch.n_br_pc;
            issue.branch_pred_pc = isif.dispatch.n_br_pred;
            issue.rd = fusif.fust.op[i].rd;
            issue.spec = ((i==0 || i==1) && !isif.branch_resolved && !isif.branch_miss) ? fusif.fust.op[i].spec : '0; // pretty sure only on alu instr
            issue.j_type = fusif.fust.op[i].j_type;
          end else if (i == 3) begin // matrix ld/st
            issue.md = fumif.fust.op.md;
            issue.ls_in = fumif.fust.op.mem_type;
            s_rs1 = fumif.fust.op.rs1;
            issue.fu_en[i] = 1'b1;
            imm = fumif.fust.op.imm;
          end else if (i == 4) begin // gemm
            issue.md  = fugif.fust.op.md;
            issue.ms1 = fugif.fust.op.ms1;
            issue.ms2 = fugif.fust.op.ms2;
            issue.ms3 = fugif.fust.op.ms3;
            issue.gemm_new_weight = fugif.fust.op.new_weight; 
            issue.fu_en[i] = 1'b1;
          end
          issue.rdat1 = (lui_type) ? '0 : rfif.rdat1;
          issue.rdat2 = (i_type && (fusif.fust.op[i].mem_type == scalar_na) && (issue.fu_en[2] != 1'b1)) ? imm : rfif.rdat2;
          issue.imm = imm;
        end
      end
    end

    // fusts are sent back to dispatch - connected in scoreboard.sv
    always_comb begin : Dispatch_Loopback
      isif.fust_s = fusif.fust;
      isif.fust_m = fumif.fust;
      isif.fust_g = fugif.fust;
    end

endmodule
