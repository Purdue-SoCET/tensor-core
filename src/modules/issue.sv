// fust gets written do in dispatch on clock edge
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

    // Local Variables
    logic hazard;
    fust_s_t fust_s;
    fust_m_t fust_m;
    fust_g_t fust_g;
    issue_t n_issue;
    issue_t issue;
    regbits_t s_rs1, s_rs2;
    logic [4:0] incoming_instr;

    logic [4:0] rdy;
    logic [4:0] n_rdy;
    logic [4:0][1:0] age;
    logic [4:0][1:0] n_age;
    fust_state_e [4:0] fust_state;
    fust_state_e [4:0] next_fust_state;
    logic [4:0] oldest_rdy;
    logic [4:0] next_oldest_rdy;
    logic [1:0] oldest_age;
    logic [1:0] next_oldest_age;

    always_comb begin : Incoming_Instr_Logic
      incoming_instr = '0;
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
      

    always_ff @ (posedge CLK, negedge nRST) begin: Pipeline_Latching
      if (~nRST)
        isif.out <= '0;
    	else
        isif.out <= n_issue;
    end

    always_comb begin : Pipeline_Output
      case (1'b1)
        isif.freeze: n_issue = isif.out; //need to think of cases for freezes/flushes
        default:     n_issue = issue;
      endcase
    end

    always_comb begin : Regfile
      rfif.WEN   = isif.wb.s_rw_en;
      rfif.wsel  = isif.wb.s_rw;
      rfif.wdata = isif.s_wdata;
      rfif.rsel1 = s_rs1;
      rfif.rsel2 = s_rs2;
    end

    always_comb begin : FUST
      // this needs verified, only dispatch writes to the FUST, but on a wb
      // complete, the row should be made available for a new isntruction.
      // Right now the table doesnt get cleared, but the busy bit gets cleared
      // by the issue stage which should allow dispatch to overwrite it.
      fusif.en       = isif.n_fust_s_en;
      fusif.fu       = isif.n_fu_s;
      fusif.fust_row = isif.n_fust_s;
      fusif.busy[0]  = (fust_state[0] == FUST_EX && (next_fust_state[0] == FUST_EMPTY || next_fust_state[0] == FUST_WAIT)) ? 1'd0 : next_fust_state[0] != FUST_EMPTY;
      fusif.busy[1]  = (fust_state[1] == FUST_EX && (next_fust_state[1] == FUST_EMPTY || next_fust_state[1] == FUST_WAIT)) ? 1'd0 : next_fust_state[1] != FUST_EMPTY;
      fusif.busy[2]  = (fust_state[2] == FUST_EX && (next_fust_state[2] == FUST_EMPTY || next_fust_state[2] == FUST_WAIT)) ? 1'd0 : next_fust_state[2] != FUST_EMPTY;

      fumif.en       = isif.n_fust_m_en;
      fumif.fust_row = isif.n_fust_m;
      fumif.busy     = next_fust_state[3] != FUST_EMPTY;

      fugif.en       = isif.n_fust_g_en;
      fugif.fust_row = isif.n_fust_g;
      fugif.busy     = next_fust_state[4] != FUST_EMPTY;
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Age_Latch
      if (~nRST)
        age <= '0;
      else
        age <= n_age;
    end

    always_comb begin : Age_Logic
      n_age = age;
      for (int i = 0; i < 5; i++) begin
        case (fust_state[i])
          FUST_EMPTY: n_age[i] = {1'b0,incoming_instr[i]}; // set new instructions to age 1
          FUST_WAIT:  n_age[i] = age[i] + 1;
          FUST_RDY:   n_age[i] = age[i] + 1;
          FUST_EX:    n_age[i] = '0;
          default: n_age = age;
        endcase
      end
    end
    
    always_ff @ (posedge CLK, negedge nRST) begin: Oldest_Latch
      if (~nRST) begin
        oldest_age <= '0;
        oldest_rdy <= '0;
      end else begin
        oldest_age <= next_oldest_age;
        oldest_rdy <= next_oldest_rdy;
      end
    end

    always_comb begin : Oldest_Logic
      next_oldest_age = oldest_age;
      next_oldest_rdy = oldest_rdy;
      for (int i = 0; i < 5; i++) begin
        if (n_rdy[i] & (n_age[i] > oldest_age)) begin
          next_oldest_age = age[i];
          next_oldest_rdy = '0;
          next_oldest_rdy[i] = 1'b1;
        end
      end
    end

    always_ff @ (posedge CLK, negedge nRST) begin: Ready_Latch
      if (~nRST)
        rdy <= '0;
      else
        rdy <= n_rdy;
    end

    always_comb begin : Ready_Logic
      n_rdy = rdy;
      for (int i = 0; i < 5; i++) begin
        case (fust_state[i])
          FUST_EMPTY: n_rdy[i] = 1'b0;
          FUST_WAIT: begin // implies instruction is already loaded
            if (i < 3) begin // Scalar FUST
              n_rdy[i] = (~|fusif.fust.op[i].t1 & ~|fusif.fust.op[i].t2);
            end else if (i == 3) begin // Matrix LD/ST FUST
              n_rdy[i] = (~|fumif.fust.op.t1 & ~|fumif.fust.op.t2);
            end else if (i == 4) begin // GEMM FUST
              n_rdy[i] = (~|fugif.fust.op.t1 & ~|fugif.fust.op.t2 & ~|fugif.fust.op.t3);
            end
          end
          // I think just let FUST_RDY state get its rdy bit resolved in EX if
          // output logic is going to depend on n_rdy, clearing it in RDY
          // wont let it issue
          //FUST_RDY:
          FUST_EX: n_rdy[i] = 1'b0;
          default: n_rdy[i] = rdy[i];
        endcase
      end
    end

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
        case (fust_state[i])
          FUST_EMPTY: begin
            next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
          end
          FUST_WAIT: begin
            if (n_rdy[i])
              next_fust_state[i] = (n_rdy[i] == next_oldest_rdy[i]) ? FUST_EX : FUST_RDY;
          end
          FUST_RDY: begin
            next_fust_state[i] = (next_oldest_rdy[i]) ? FUST_EX : FUST_RDY;
          end
          FUST_EX: begin
            //TODO:handle flushing on speculation

            if (isif.wb.s_rw_en & isif.wb.alu_done & (i == 0)) begin
              next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
              // TODO 
              fusif.fust.op[1].t1 = (fusif.fust.op[1].t1 == 2'd1) && fusif.busy[1] ? '0 : fusif.fust.op[1].t1;
              fusif.fust.op[1].t2 = (fusif.fust.op[1].t2 == 2'd1) && fusif.busy[1] ? '0 : fusif.fust.op[1].t2;
              fusif.fust.op[2].t1 = (fusif.fust.op[2].t1 == 2'd1) && fusif.busy[2] ? '0 : fusif.fust.op[2].t1;
              fusif.fust.op[2].t2 = (fusif.fust.op[2].t2 == 2'd1) && fusif.busy[2] ? '0 : fusif.fust.op[2].t2;
            end else if (isif.wb.s_rw_en & isif.wb.load_done & (i == 1)) begin
              next_fust_state[i] = incoming_instr[i] ? FUST_WAIT : FUST_EMPTY;
              // TODO 
              fusif.fust.op[0].t1 = (fusif.fust.op[0].t1 == 2'd2) && fusif.busy[0] ? '0 : fusif.fust.op[0].t1;
              fusif.fust.op[0].t2 = (fusif.fust.op[0].t2 == 2'd2) && fusif.busy[0] ? '0 : fusif.fust.op[0].t2;
              fusif.fust.op[2].t1 = (fusif.fust.op[2].t1 == 2'd2) && fusif.busy[2] ? '0 : fusif.fust.op[2].t1;
              fusif.fust.op[2].t2 = (fusif.fust.op[2].t2 == 2'd2) && fusif.busy[2] ? '0 : fusif.fust.op[2].t2;
            end
            //TODO: handle dones from branch and matrix FUs

            // WAR HANDLING
            //writing to reg A, where an older FUST thats in RDY or WAIT (hasnt
            //read register) needs to stall the write to A until all reads to
            //reg A are in EX
            
            // TODO: need stall signals for the execute FUs if next_fust_state
            // is stalled in EX
            if ((i == 0 & (fusif.fust.op[1].t1 == 2'd0 | fusif.fust.op[1].t2 == 2'd0)) &
                (fust_state[1] == FUST_WAIT | fust_state[1] == FUST_RDY) &
                age[1] > age[0]) begin
              // stall ALU from writing
              next_fust_state[i] = FUST_EX;
            end
            if ((i == 1 & (fusif.fust.op[0].t1 == 2'd1 | fusif.fust.op[0].t2 == 2'd1) &&
                (fust_state[0] == FUST_WAIT | fust_state[0] == FUST_RDY) &&
                age[0] > age[1])) begin
              // stall LD/ST from writing
              next_fust_state[i] = FUST_EX;
            end
          end
          default: begin
            next_fust_state = fust_state;
          end
        endcase
      end
    end

    always_comb begin : Output_Logic
      issue = isif.out;
      s_rs1 = '0;
      s_rs2 = '0;
      for (int i = 0; i < 5; i++) begin
        //TODO:verify this will only ever apply to one instruction per cycle
        if (fust_state[i] != FUST_EX & next_fust_state[i] == FUST_EX) begin
          // issue this instruction
          // TODO: add opcode to be sent to FUs
          if (i < 3) begin
            s_rs1 = fusif.fust.op[i].rs1;
            s_rs2 = fusif.fust.op[i].rs2;
            issue.fu_en = i[2:0];
          end else if (i == 3) begin
            s_rs1 = fumif.fust.op.rs1;
            s_rs2 = fumif.fust.op.rs2;
            issue.fu_en = i[2:0];
          end else if (i == 4) begin
            issue.ms1 = fugif.fust.op.ms1;
            issue.ms2 = fugif.fust.op.ms2;
            issue.ms3 = fugif.fust.op.ms3;
            issue.fu_en = i[2:0];
          end
          issue.rdat1 = rfif.rdat1;
          issue.rdat2 = rfif.rdat2;
        end
      end
    end

    always_comb begin : Dispatch_Loopback
      isif.fust_s = fusif.fust;
      isif.fust_m = fumif.fust;
      isif.fust_g = fugif.fust;
    end

endmodule
