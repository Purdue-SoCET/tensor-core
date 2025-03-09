`include "dispatch_if.vh"
`include "types_pkg.vh"

module dispatch(
    input logic CLK, nRST,
    dispatch_if.DI diif
);

    import types_pkg::*;

    dispatch_t n_dispatch;
    dispatch_t dispatch;

    // hazards
    logic WAW_h;
    logic struct_h;
    logic harzard;

    always_ff @ (posedge CLK, negedge nRST) begin: Pipeline Latching
      if (~nRST)
        diif.out <= '0;
    	else
        diif.out <= n_dispatch;
    end

    always_comb begin : Pipeline Output
      case (1'b1)
        diif.flush:  n_dispatch = '0;
        diif.freeze: n_dispatch = diif.out;
        hazard:      n_dispatch = diif.out;
        diif.ihit:   n_dispatch = dispatch;
        default:     n_dispatch = diif.out;
      endcase
    end

    always_comb begin: Instruction Signals
      Instruction = diif.fetch.imemload;
      op = opcode_t'(Instruction[31:26]);
      rs = Instruction[25:21];
      rt = Instruction[20:16];
      rd = Instruction[15:11];
      imm = Instruction[15:0];
      func = funct_t'(Instruction[5:0]);
    end

    always_comb begin : Hazard Logic
      case (cuif.cu.fu)
        ALU: struct_h = fust.alu.busy;
        LDST: struct_h = fust.ldst.busy;
        BRANCH: struct_h = fust.branch.busy;
        default: struct_h = 1'b0;
      endcase
      WAW_h = rst[rd].busy;
      hazard = struct_h | WAW_h;
    end

    always_comb begin : Dispatch Out
      dispatch = diif.fetch.out;
      dispatch.hazard = hazard;
      dispatch.cu = cuif.cu;
    end

endmodule
