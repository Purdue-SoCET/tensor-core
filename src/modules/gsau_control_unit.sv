`include "gsau_control_unit_if.vh"
`include "sys_arr_pkg.vh"
`include "vector_pkg.vh"

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

  // local constants
  localparam int ENTRY_BITS = $clog2(VEGGIEREGS);
  localparam int FIFO_DEPTH = (FIFOSIZE / ENTRY_BITS);

  // FIFO interface signals
  logic         fifo_wr, fifo_rd;
  logic [ENTRY_BITS-1:0] fifo_din;
  logic [ENTRY_BITS-1:0] fifo_dout;
  logic         fifo_empty, fifo_full;

  // // captured instruction fields
  // logic [7:0]   captured_vdst;
  // logic         captured_weight;

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

  // NEXT signals for sequential outputs
  /*logic [ENTRY_BITS-1:0] latched_vdst, latched_vdst_next;
  logic [7:0] o_wb_wbdst_next, o_sb_vdst_next;
  logic o_wb_valid_next, o_sb_valid_next; */

  // alias interface signals for clarity
  // From Veggie File
  vreg_t               veg_vs1      = gsau_port.veg_vs1;
  vreg_t               veg_psums      = gsau_port.veg_vs2;
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
  logic                sa_out_valid       = gsau_port.sa_out_valid;
  logic                sa_fifo_has_space = gsau_port.sa_fifo_has_space;
  logic                o_sa_output_ready = gsau_port.sa_output_ready;

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

  always_comb begin
    fifo_wr        = 1'b0;
    fifo_rd        = 1'b0;
    fifo_din       = '0;

    // captured_vdst  = '0;
    // captured_weight = 1'b0;

    o_sa_array_in         = veg_vs1; // send either activations or weights
    o_sa_array_in_partials = veg_vs2; // always send partials, but only valid when inputs are loaded
    o_sa_input_en         = 1'b0;
    o_sa_weight_en        = 1'b0;
    o_sa_partial_en       = 1'b0;

    o_wb_wbdst = din;
    o_wb_psum = sa_array_output;

    // o_wb_psum   = '0;
    // o_wb_wbdst  = '0;
    // o_wb_valid   = 1'b0;

    // o_sb_ready  = 1'b0;
    // o_sb_vdst   = '0;
    // o_sb_valid  = 1'b0;

    // o_veg_ready = 1'b0;

    // Default handshake semantics:
    // - sb_ready asserted when FIFO not full (we can accept more RD's)
    // - veg_ready asserted when FIFO not full AND SA input FIFO has space (simple backpressure)
    o_sb_ready  = !fifo_full && sa_fifo_has_space; // allow scoreboard to send new inst when space
    o_sa_output_ready = wb_output_ready
    //o_veg_ready = (!fifo_full) && sa_fifo_has_space;


    if (sb_valid && veg_valid && o_sb_ready) begin
      if (sb_weight) begin
        // LOAD WEIGHTS
        o_sa_weight_en = 1'b1;
      end else begin
        din = sb_vdst; // push to fifo
        fifo_wr = 1'b1;
        o_sa_input_en = 1'b1;
        o_sa_partial_en = 1'b1;
      end
    end

    if (sa_out_valid && sa_output_ready) begin
      fifo_rd = 1'b1;
      o_wb_valid = 1'b1;
    end

  end

endmodule