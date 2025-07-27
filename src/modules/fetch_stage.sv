`include "fetch_stage_if.vh"
`include "fetch_if.vh"
`include "fu_branch_predictor_if.vh"
`include "isa_types.vh"

module fetch_stage(
  input logic CLK, nRST, ihit,
  fetch_stage_if.fs fsif
);
  import isa_pkg::*;

  word_t prev_pc, prev_instr;
  logic prev_pred;

  word_t save_pc, pc_change;
  logic miss_pred, missed;

  //Instantiation interfaces   
  fetch_if fif();
  fu_branch_predictor_if btbif();

  //-------------------------------------------
  // Fetch unit connections 
  assign fif.imemload      = fsif.imemload;           // Input from memory
  assign fif.freeze        = fsif.freeze || fsif.jump;  // Input from scoreboard
  assign fif.jump          = fsif.jump;
  assign fif.misprediction = fsif.misprediction; // Input from branch predictor
  assign fif.correct_pc    = fsif.correct_pc;       // Input from branch predictor
  assign fif.br_jump       = fsif.br_jump;
  assign fif.missed        = missed;
  assign fsif.imemREN      = fif.imemREN;             // Output to memory
  assign fsif.imemaddr     = fif.imemaddr;           // Output to memory
  //-------------------------------------------

  //-------------------------------------------
  // we latch prev inst info for freeze support
  always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
      prev_pc <= '0;
      prev_instr <= '0;
      prev_pred <= '0;
    end
    else if (!fsif.freeze) begin
      prev_pc <= fif.pc;
      prev_instr <= fif.instr;
      prev_pred <= btbif.predicted_outcome;
    end
  end
  //-------------------------------------------

  //-------------------------------------------
  // divided instruction and pc forwarding into 4 cases
  always_comb begin
    pc_change = save_pc;
    miss_pred = missed;

    // Case 1: halt
    if (fsif.halt) begin
      fsif.pc    = '0;
      fsif.instr = '0;

    // Case 2: branch misprediction + BTB update
    end else if (fsif.update_btb && fsif.misprediction) begin
      pc_change = fsif.correct_pc;
      miss_pred = 1;
      fsif.pc    = '0;
      fsif.instr = '0;

    // Case 3: resolving prior miss
    end else if (missed) begin
      if (save_pc == fif.pc) begin
        pc_change = '0;
        miss_pred = 0;
        fsif.pc   = (fsif.freeze) ? prev_pc : fif.pc;
        fsif.instr = (fsif.freeze) ? prev_instr : fif.instr;
      end else begin
        fsif.pc    = '0;
        fsif.instr = '0;
      end

    // Case 4: normal fetch
    end else begin
      if (fsif.freeze) begin
        fsif.pc    = prev_pc;
        fsif.instr = prev_instr;
      end else if (fsif.jump) begin
        fsif.pc    = '0;
        fsif.instr = '0;
      end else begin
        fsif.pc    = fif.pc;
        fsif.instr = fif.instr;
      end
    end
  end
  //-------------------------------------------

  always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
      save_pc <= '0;
      missed <= '0;
    end
    else begin
      save_pc <= pc_change;
      missed <= miss_pred;
    end
  end

  //-------------------------------------------
  // Branch predictor connections
  assign btbif.pc = fif.pc;
  assign btbif.update_btb = fsif.update_btb;
  assign btbif.branch_outcome = fsif.branch_outcome;
  assign btbif.update_pc = fsif.update_pc;
  assign btbif.branch_target = fsif.branch_target;
  assign btbif.imemaddr = fif.imemaddr;

  assign fsif.predicted_outcome = (fsif.freeze) ? prev_pred : btbif.predicted_outcome;
  //-------------------------------------------

  // Module instances
  fetch fetch_unit (
    .CLK(CLK),
    .nRST(nRST),
    .ihit(ihit),
    .fif(fif.ft)
  );

  fu_branch_predictor predictor (
    .CLK(CLK),
    .nRST(nRST),
    .ihit(ihit),
    .fubpif(btbif.btb)
  );

  assign fif.pc_prediction = btbif.predicted_target;
endmodule