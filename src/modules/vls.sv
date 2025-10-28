`include "vector_types.vh"
`include "vector_if.vh"
`include "vls_if.vh"

module vls (
  input  logic    CLK,
  input  logic    nRST,
  vls_if.vls      vlsif
);
  import vector_pkg::*;

  localparam int FIFO_DEPTH_VD   = 8;              
  localparam int VEC_ELEMS       = 32;             
  localparam int ELEM_W          = 32;             // 32-bit element
  localparam int VEC_W           = VEC_ELEMS*ELEM_W; // 1024-bit packed vector
  localparam int FIFO_DEPTH_DATA = 8;              // 8 stored vectors per lane

  // VD Fifos
  logic        fifo_full_a,  fifo_empty_a,  fifo_shift_a,  fifo_wr_a;
  logic [3:0]  fifo_dout_a;

  logic        fifo_full_b,  fifo_empty_b,  fifo_shift_b,  fifo_wr_b;
  logic [3:0]  fifo_dout_b;

  // Issue Conditions
  logic can_issue_a, can_issue_b;
  assign can_issue_a = (vlsif.valid && vlsif.op == 7'b0100111 && !fifo_full_a);
  assign can_issue_b = (vlsif.valid && vlsif.op == 7'b0100111 && !fifo_full_b);

  // Any Outstanding Requests
  logic any_outstanding;
  assign any_outstanding = !(fifo_empty_a && fifo_empty_b);

  //
  typedef enum logic [1:0] { IDLE, DATA } state_t;
  state_t state, next_state;

  // Registered Inputs
  logic [7:0]  imm_a_r, imm_b_r;
  logic [3:0]  vd_a_r, vd_b_r;
  logic [4:0]  rs1_a_r, rs1_b_r;
  logic        row_col_a_r, row_col_b_r;
  logic [5:0]  num_rows_a_r, num_rows_b_r, num_cols_a_r, num_cols_b_r;
  logic        id_a_r, id_b_r;
  logic [6:0]  op_r;
  logic [3:0]  v2_a_r, v2_b_r;

  logic [15:0] addr_a_n, addr_b_n;

  //VD Fifos
  vls_fifo #(.FIFODEPTH(FIFO_DEPTH_VD), .DATAWIDTH(4)) qA (
    .nRST  (nRST), .CLK(CLK),
    .wr_en (fifo_wr_a), .shift(fifo_shift_a),
    .din   (vlsif.vd_a), .dout(fifo_dout_a),
    .empty (fifo_empty_a), .full(fifo_full_a)
  );
  vls_fifo #(.FIFODEPTH(FIFO_DEPTH_VD), .DATAWIDTH(4)) qB (
    .nRST  (nRST), .CLK(CLK),
    .wr_en (fifo_wr_b), .shift(fifo_shift_b),
    .din   (vlsif.vd_b), .dout(fifo_dout_b),
    .empty (fifo_empty_b), .full(fifo_full_b)
  );

  assign fifo_wr_a    = can_issue_a;
  assign fifo_wr_b    = can_issue_b;
  assign fifo_shift_a = (state == DATA) && vlsif.vec_res && !fifo_empty_a;
  assign fifo_shift_b = (state == DATA) && vlsif.vec_res && !fifo_empty_b;

  // Pack/unpack wires
  logic [VEC_W-1:0] load_vec_a_packed, load_vec_b_packed;
  logic [VEC_W-1:0] out_vec_a_packed,  out_vec_b_packed;

  // Pack arrays from IF into 1024-bit
  integer i;
  always_comb begin
    for (i = 0; i < VEC_ELEMS; i++) begin
      load_vec_a_packed[i*ELEM_W +: ELEM_W] = vlsif.load_data_a[i];
      load_vec_b_packed[i*ELEM_W +: ELEM_W] = vlsif.load_data_b[i];
    end
  end

  // Data FIFOs
  logic                 d_full_a, d_empty_a, d_shift_a, d_wr_a;
  logic [VEC_W-1:0]     d_dout_a;

  logic                 d_full_b, d_empty_b, d_shift_b, d_wr_b;
  logic [VEC_W-1:0]     d_dout_b;

  vls_fifo #(.FIFODEPTH(FIFO_DEPTH_DATA), .DATAWIDTH(VEC_W)) dA (
    .nRST  (nRST), .CLK(CLK),
    .wr_en (d_wr_a), .shift(d_shift_a),
    .din   (load_vec_a_packed), .dout(d_dout_a),
    .empty (d_empty_a), .full(d_full_a)
  );

  vls_fifo #(.FIFODEPTH(FIFO_DEPTH_DATA), .DATAWIDTH(VEC_W)) dB (
    .nRST  (nRST), .CLK(CLK),
    .wr_en (d_wr_b), .shift(d_shift_b),
    .din   (load_vec_b_packed), .dout(d_dout_b),
    .empty (d_empty_b), .full(d_full_b)
  );

  // When downstream is stalled, capture incoming vectors on vec_res edges
  logic stall = ~vlsif.ready_in;

  assign d_wr_a   = stall && vlsif.vec_res && !d_full_a;
  assign d_wr_b   = stall && vlsif.vec_res && !d_full_b;

  // If there are buffered vectors, drain FIFO first (one vector per vec_res)
  //  - Else passthrough current vector
  assign d_shift_a = (!stall) && vlsif.vec_res && !d_empty_a;
  assign d_shift_b = (!stall) && vlsif.vec_res && !d_empty_b;

  // Choose outputs (packed)
  always_comb begin
    if (!stall && !d_empty_a) out_vec_a_packed = d_dout_a;               // drain
    else                      out_vec_a_packed = load_vec_a_packed;       // passthrough

    if (!stall && !d_empty_b) out_vec_b_packed = d_dout_b;
    else                      out_vec_b_packed = load_vec_b_packed;
  end

  // Unpack to sp_load_data
  integer j;
  always_comb begin
    for (j = 0; j < VEC_ELEMS; j++) begin
      vlsif.sp_load_data_a[j] = out_vec_a_packed[j*ELEM_W +: ELEM_W];
      vlsif.sp_load_data_b[j] = out_vec_b_packed[j*ELEM_W +: ELEM_W];
    end
  end

  // pull ready_out low when stalled or when either data FIFO is full
  always_comb begin
    vlsif.ready_out = vlsif.ready_in && !d_full_a && !d_full_b;
  end

  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      state <= IDLE;
      imm_a_r <= '0; imm_b_r <= '0;
      vd_a_r  <= '0; vd_b_r  <= '0;
      rs1_a_r <= '0; rs1_b_r <= '0;
      row_col_a_r <= '0; row_col_b_r <= '0;
      num_rows_a_r <= '0; num_rows_b_r <= '0;
      num_cols_a_r <= '0; num_cols_b_r <= '0;
      id_a_r <= '0; id_b_r <= '0;
      op_r <= '0;
      v2_a_r <= '0; v2_b_r <= '0;
    end
    else begin
      state <= next_state;
      if (state == IDLE && vlsif.valid) begin
        imm_a_r <= vlsif.imm_a;     imm_b_r <= vlsif.imm_b;
        vd_a_r  <= vlsif.vd_a;      vd_b_r  <= vlsif.vd_b;
        rs1_a_r <= vlsif.rs1_a;     rs1_b_r <= vlsif.rs1_b;
        row_col_a_r <= vlsif.row_col_a;  row_col_b_r <= vlsif.row_col_b;
        num_rows_a_r <= vlsif.num_rows_a; num_rows_b_r <= vlsif.num_rows_b;
        num_cols_a_r <= vlsif.num_cols_a; num_cols_b_r <= vlsif.num_cols_b;
        id_a_r  <= vlsif.id_a;      id_b_r  <= vlsif.id_b;
        op_r    <= vlsif.op;
        v2_a_r  <= vlsif.v2_a;      v2_b_r  <= vlsif.v2_b;
      end
    end
  end

  always_comb begin
    // Defaults
    vlsif.sp_store_data_a = '0;
    vlsif.sp_store_data_b = '0;

    vlsif.wb_vd_a = '0;
    vlsif.wb_vd_b = '0;

    next_state           = state;
    vlsif.sp_op          = vlsif.op;
    vlsif.sp_row_col_a   = vlsif.row_col_a;
    vlsif.sp_row_col_b   = vlsif.row_col_b;
    vlsif.sp_num_rows_a  = vlsif.num_rows_a;
    vlsif.sp_num_rows_b  = vlsif.num_rows_b;
    vlsif.sp_num_cols_a  = vlsif.num_cols_a;
    vlsif.sp_num_cols_b  = vlsif.num_cols_b;
    vlsif.sp_id_a        = vlsif.id_a;
    vlsif.sp_id_b        = vlsif.id_b;

    // Address calc
    addr_a_n = {8'b0, vlsif.rs1_a} + {8'b0, vlsif.imm_a};
    addr_b_n = {8'b0, vlsif.rs1_b} + {8'b0, vlsif.imm_b};
    vlsif.sp_addr_a = addr_a_n;
    vlsif.sp_addr_b = addr_b_n;

    // Transfer the vector destination register on vec_res`
    if (state == DATA && vlsif.vec_res) begin
      if (!fifo_empty_a) vlsif.wb_vd_a = fifo_dout_a;
      if (!fifo_empty_b) vlsif.wb_vd_b = fifo_dout_b;
    end

    // State machine
    case (state)
      IDLE: begin
        if (vlsif.valid) begin
          if (vlsif.op == 7'b0100111 || vlsif.op == 7'b0101000)
            next_state = DATA;
        end
      end
      DATA: begin
        if (!any_outstanding &&
            !(vlsif.valid && (vlsif.op == 7'b0100111 || vlsif.op == 7'b0101000))) begin
          next_state = IDLE;
        end
      end
    endcase
  end
endmodule