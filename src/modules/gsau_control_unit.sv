`include "gsau_control_unit_if.vh"

module gsau_control_unit #(
    parameter int VEGGIEREGS = 256,
    // FIFOSIZE is in bits in your design notes (32 regs * 3 * 8 = 768 bits).
    // We store 8-bit vdst entries -> FIFO_DEPTH = FIFOSIZE / 8 = number of entries.
    parameter int FIFOSIZE = 32*3*8
) (
    input  logic        CLK,
    input  logic        nRST,
    gsau_control_unit_if.gsau        gsau_port
);

  import vector_pkg::*;   // reuse basic typedefs (data, addr, etc.)
  import sys_arr_pkg::*;  // systolic-specific typedefs
  import types_pkg::*;

  // local constants
  localparam int ENTRY_BITS = 8;
  localparam int FIFO_DEPTH = (FIFOSIZE / ENTRY_BITS);

  typedef enum logic [2:0] {
    IDLE         = 3'd0,
    ACCEPT_INST  = 3'd1, // accept scoreboard + veggie data and issue to SA
    WAIT_OUTPUT  = 3'd2, // waiting for SA to produce output
    SEND_OUTPUT  = 3'd3  // drive WB with psum + vdst until accepted
  } state_t;

  // internal registers
  state_t       state, next_state;

  // FIFO interface signals
  logic         fifo_wr, fifo_rd;
  logic [ENTRY_BITS-1:0] fifo_din;
  logic [ENTRY_BITS-1:0] fifo_dout;
  logic         fifo_empty, fifo_full;

  // captured instruction fields
  logic [7:0]   captured_vdst;
  logic         captured_weight;

  // outputs that we drive (local registered versions)
  logic [511:0] o_sa_array_in;
  logic [511:0] o_sa_array_in_partials;
  logic         o_sa_input_en;
  logic         o_sa_weight_en;
  logic         o_sa_partial_en;

  logic [511:0] o_wb_psum;
  logic [7:0]   o_wb_wbdst;
  logic         o_wb_valid;

  logic         o_sb_ready;
  logic [7:0]   o_sb_vdst;
  logic         o_sb_valid;

  logic         o_veg_ready;

  // alias interface signals for clarity
  // From Veggie File
  vreg_t               veg_vdata      = gsau_port.veg_vdata;
  logic                veg_valid      = gsau_port.veg_valid;
  // To Veggie File
  // veg_ready driven below

  // Scoreboard -> GSAU
  logic                sb_nready      = gsau_port.sb_nready;
  logic [7:0]          sb_nvdst       = gsau_port.sb_nvdst;
  logic                sb_nvalid      = gsau_port.sb_nvalid;
  logic                sb_weight      = gsau_port.sb_weight;

  // WB Buffer -> GSAU
  logic                wb_output_ready = gsau_port.wb_output_ready;

  // Systolic Array -> GSAU
  logic [511:0]        sa_array_output = gsau_port.sa_array_output;
  logic                sa_out_en       = gsau_port.sa_out_en;
  logic                sa_fifo_has_space = gsau_port.sa_fifo_has_space;

  // Connect internal outputs to interface (final assignments)
  assign gsau_port.sa_array_in          = o_sa_array_in;
  assign gsau_port.sa_array_in_partials = o_sa_array_in_partials;
  assign gsau_port.sa_input_en          = o_sa_input_en;
  assign gsau_port.sa_weight_en         = o_sa_weight_en;
  assign gsau_port.sa_partial_en        = o_sa_partial_en;

  assign gsau_port.wb_psum   = o_wb_psum;
  assign gsau_port.wb_wbdst  = o_wb_wbdst;
  assign gsau_port.wb_valid  = o_wb_valid;

  assign gsau_port.sb_ready  = o_sb_ready;
  assign gsau_port.sb_vdst   = o_sb_vdst;
  assign gsau_port.sb_valid  = o_sb_valid;

  assign gsau_port.veg_ready = o_veg_ready;

  // module sync_fifo #(parameter FIFODEPTH=8, DATAWIDTH=16) (
  //   input logic rstn, clk, wr_en, rd_en,
  //   input logic [DDATAWIDTH-1:0] din,
  //   output logic [DDATAWIDTH-1:0] dout,
  //   output logic empty, full
  // );
  sync_fifo #(
    .FIFODEPTH(FIFO_DEPTH),
    .DATAWIDTH(ENTRY_BITS)
  ) rd_fifo (
    .rstn(nRST),
    .clk(CLK),
    .wr_en(fifo_wr),
    .rd_en(fifo_rd),
    .din(fifo_din),
    .dout(fifo_dout),
    .empty(fifo_empty),
    .full(fifo_full)
  );

  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  always_comb begin
    next_state = state;

    fifo_wr        = 1'b0;
    fifo_rd        = 1'b0;
    fifo_din       = '0;

    captured_vdst  = '0;
    captured_weight = 1'b0;

    o_sa_array_in         = '0;
    o_sa_array_in_partials= '0;
    o_sa_input_en         = 1'b0;
    o_sa_weight_en        = 1'b0;
    o_sa_partial_en       = 1'b0;

    o_wb_psum   = '0;
    o_wb_wbdst  = '0;
    o_wb_valid   = 1'b0;

    o_sb_ready  = 1'b0;
    o_sb_vdst   = '0;
    o_sb_valid  = 1'b0;

    o_veg_ready = 1'b0;

    // Default handshake semantics:
    // - sb_ready asserted when FIFO not full (we can accept more RD's)
    // - veg_ready asserted when FIFO not full AND SA input FIFO has space (simple backpressure)
    o_sb_ready  = !fifo_full;                 // allow scoreboard to send new inst when space
    o_veg_ready = (!fifo_full) && sa_fifo_has_space;

    case (state)
      IDLE: begin
        // Wait for next instruction from scoreboard (sb_nvalid) and data from veggie (veg_valid).
        // We accept instruction when scoreboard presents a valid vdst and veggie has valid data.
        // Also sb_nready is an input from scoreboard side; we don't depend on it here (it's their readiness)
        if (sb_nvalid && veg_valid && o_sb_ready && o_veg_ready) begin
          // Accept instruction: write vdst into FIFO and issue data to systolic array
          fifo_wr   = 1'b1;
          fifo_din  = sb_nvdst;

          // decide based on weight flag
          if (sb_weight) begin
            o_sa_array_in = veg_vdata;      // weight payload on array_in for weight path
            o_sa_weight_en = 1'b1;
          end else begin
            o_sa_array_in = veg_vdata;
            o_sa_input_en  = 1'b1;
          end

          // after issuing, move to WAIT_OUTPUT to wait for SA to produce result
          next_state = WAIT_OUTPUT;
        end else begin
          // remain in IDLE
          next_state = IDLE;
        end
      end // IDLE

      WAIT_OUTPUT: begin
        // Waiting for systolic array to assert sa_out_en (result ready)
        // If sa_out_en appears, read vdst out of FIFO and prepare to send to WB
        if (sa_out_en && !fifo_empty) begin
          fifo_rd = 1'b1; // pop destination corresponding to produced output
          // drive writeback outputs for one cycle (or until wb accepts)
          o_wb_psum  = sa_array_output;
          // We cannot directly use fifo_dout in always_comb if FIFO produces dout registered on read,
          // but this FIFO returns dout synchronous when rd_en asserted (dout updated on rising edge in module).
          // To be safe, we'll latch fifo_dout in sequential block below and then assert wb_valid there.
          o_wb_valid = 1'b1;
          // move to SEND_OUTPUT to manage handshake with WB buffer
          next_state = SEND_OUTPUT;
        end else begin
          // Stay here until SA produces output
          next_state = WAIT_OUTPUT;
        end
      end // WAIT_OUTPUT

      SEND_OUTPUT: begin
        // Attempt to send output to WB buffer. Wait until WB accepts (wb_output_ready).
        // When wb_output_ready is asserted we consider transaction complete and go back to IDLE.
        // NOTE: o_wb_wbdst must come from fifo_dout captured in sequential logic below.
        o_wb_psum  = sa_array_output; // continue driving current PSUM until accepted
        o_wb_valid = 1'b1;

        if (wb_output_ready) begin
          // WB accepted output; return to IDLE to accept next instruction
          next_state = IDLE;
        end else begin
          next_state = SEND_OUTPUT;
        end
      end // SEND_OUTPUT

      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // Sequential block to latch fifo output and drive WB/scoreboard outputs that require registered values.
  // The idea: fifo_dout is updated by FIFO on read, but it's safe to capture in this always_ff and use it.
  logic [ENTRY_BITS-1:0] latched_vdst;
  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      latched_vdst <= '0;
      o_wb_wbdst   <= '0;
      o_sb_vdst    <= '0;
      o_sb_valid   <= 1'b0;
      o_wb_valid   <= 1'b0;
    end else begin
      // capture FIFO dout when fifo_rd is asserted (we popped)
      if (fifo_rd) begin
        latched_vdst <= fifo_dout;
      end

      // Manage wb_valid and wb_wbdst: when in SEND_OUTPUT we keep driving until WB accepts
      if (state == SEND_OUTPUT) begin
        o_wb_wbdst <= latched_vdst;
        // o_wb_valid is driven combinationally as 1 in SEND_OUTPUT; to reflect it in sequential,
        // keep it high until wb_output_ready is seen.
        if (wb_output_ready) begin
          o_wb_valid <= 1'b0;
          o_wb_wbdst <= '0;
        end else begin
          o_wb_valid <= 1'b1;
        end
      end else begin
        // not sending
        o_wb_valid <= 1'b0;
        o_wb_wbdst <= '0;
      end

      // Drive scoreboard outputs: indicate valid when we accepted an instruction (fifo_wr)
      if (fifo_wr) begin
        // The sb_vdst is the value scoreboard gave (sb_nvdst).
        o_sb_vdst  <= sb_nvdst;
        o_sb_valid <= 1'b1;
      end else begin
        o_sb_valid <= 1'b0;
      end
    end
  end

endmodule