`include "vector_types.vh"
`include "vector_if.vh"
`include "vls_if.vh"

module vls (
  input  logic    CLK,
  input  logic    nRST,
  vls_if.vls      vlsif
);
  import vector_pkg::*;

  typedef enum logic [1:0] { IDLE, DATA } state_t;
  state_t state, next_state;

  // Registered command fields
  logic [7:0]  imm_a_r, imm_b_r;
  logic [3:0]  vd_a_r, vd_b_r;
  logic [4:0]  rs1_a_r, rs1_b_r;
  logic        row_col_a_r, row_col_b_r;
  logic [5:0]  num_rows_a_r, num_rows_b_r, num_cols_a_r, num_cols_b_r;
  logic        id_a_r, id_b_r;
  logic [15:0] load_data_a_r, load_data_b_r;
  logic [6:0]  op_r;
  logic [3:0]  v2_a_r, v2_b_r;

  logic [15:0] addr_a_n, addr_b_n;

  always_ff @(posedge CLK or negedge nRST) begin
    if (!nRST) begin
      state <= IDLE;
      imm_a_r <= '0;
      imm_b_r <= '0;
      vd_a_r  <= '0;
      vd_b_r  <= '0;
      rs1_a_r <= '0;
      rs1_b_r <= '0;
      row_col_a_r <= '0;
      row_col_b_r <= '0;
      num_rows_a_r <= '0;
      num_rows_b_r <= '0;
      num_cols_a_r <= '0;
      num_cols_b_r <= '0;
      id_a_r <= '0;
      id_b_r <= '0;
      load_data_a_r <= '0;
      load_data_b_r <= '0;
      op_r <= '0;
      v2_a_r <= '0;
      v2_b_r <= '0;
    end else begin
      
      state <= next_state;

      // Latch command on entry (or whenever enable if you prefer)
      if (state == IDLE && vlsif.enable) begin
        imm_a_r <= vlsif.imm_a;     
        imm_b_r <= vlsif.imm_b;
        vd_a_r  <= vlsif.vd_a;      
        vd_b_r  <= vlsif.vd_b;
        rs1_a_r <= vlsif.rs1_a;     
        rs1_b_r <= vlsif.rs1_b;
        row_col_a_r <= vlsif.row_col_a;  
        row_col_b_r <= vlsif.row_col_b;
        num_rows_a_r <= vlsif.num_rows_a; 
        num_rows_b_r <= vlsif.num_rows_b;
        num_cols_a_r <= vlsif.num_cols_a; 
        num_cols_b_r <= vlsif.num_cols_b;
        id_a_r <= vlsif.id_a;       
        id_b_r <= vlsif.id_b;
        op_r   <= vlsif.op;
        v2_a_r <= vlsif.v2_a;       
        v2_b_r <= vlsif.v2_b;
      end

      // Sample load return data (if you want a stable registered copy)
      if (state == DATA && vlsif.dhit) begin
        load_data_a_r <= vlsif.load_data_a;
        load_data_b_r <= vlsif.load_data_b;
      end
    end
  end

  always_comb begin
    
    // Deafault Outputs
    next_state = state;

    vlsif.sp_store_data_a = '0;
    vlsif.sp_store_data_b = '0;
    vlsif.sp_load_data_a  = '0;
    vlsif.sp_load_data_b  = '0;

    vlsif.sp_op          = op_r;
    vlsif.sp_row_col_a   = row_col_a_r;
    vlsif.sp_row_col_b   = row_col_b_r;
    vlsif.sp_num_rows_a  = num_rows_a_r;
    vlsif.sp_num_rows_b  = num_rows_b_r;
    vlsif.sp_num_cols_a  = num_cols_a_r;
    vlsif.sp_num_cols_b  = num_cols_b_r;
    vlsif.sp_id_a        = id_a_r;
    vlsif.sp_id_b        = id_b_r;

    // Address Calculation
    addr_a_n = {8'b0, rs1_a_r} + {8'b0, imm_a_r};
    addr_b_n = {8'b0, rs1_b_r} + {8'b0, imm_b_r};
    
    vlsif.sp_addr_a = addr_a_n;
    vlsif.sp_addr_b = addr_b_n;

    // Writeback Destinations For Load
    vlsif.wb_vd_a = vd_a_r;
    vlsif.wb_vd_b = vd_b_r;

    case (state)
      IDLE: begin
        if (vlsif.enable) begin
          if (vlsif.op == STORE || vlsif.op == LOAD)
            next_state = DATA;
        end
      end

      DATA: begin
        if (vlsif.op == STORE) begin
          if (vlsif.dhit) begin
            vlsif.sp_store_data_a = v2_a_r;
            vlsif.sp_store_data_b = v2_b_r;
            next_state = IDLE;
          end
        end else if (vlsif.op == LOAD) begin
          if (vlsif.dhit) begin
            vlsif.sp_load_data_a = load_data_a_r;
            vlsif.sp_load_data_b = load_data_b_r;
            next_state = IDLE;
          end
        end
      end
    endcase
  end
endmodule
