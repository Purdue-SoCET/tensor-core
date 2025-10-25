`include "vector_types.vh"
`include "vector_if.vh"
`include "vls_if.vh"

module vls (
  input  logic    CLK,
  input  logic    nRST,
  vls_if.vls      vlsif
);
  import vector_pkg::*;

  //FIFO Signals
  localparam int FIFO_DEPTH = 8;                 //depth of fifo queue
  localparam int FIFO_AW = $clog2(FIFO_DEPTH);   //address width (num of bits for indexing into the fifo)
  logic [3:0] fifo_mem_a [FIFO_DEPTH - 1:0];
  logic [3:0] fifo_mem_b [FIFO_DEPTH - 1:0];
  logic [FIFO_AW - 1:0] fifo_head_a; //head of fifo queue a
  logic [FIFO_AW - 1:0] fifo_head_b; //head of fifo queue b
  logic [FIFO_AW - 1:0] fifo_tail_a; //tail of fifo queue a
  logic [FIFO_AW - 1:0] fifo_tail_b; //tail of fifo queue b
  logic [FIFO_AW:0] fifo_count_a;
  logic [FIFO_AW:0] fifo_count_b;
  logic fifo_full_a;
  logic fifo_full_b;
  logic fifo_empty_a;
  logic fifo_empty_b;

  assign fifo_full_a = (fifo_count_a == FIFO_DEPTH);
  assign fifo_full_b = (fifo_count_b == FIFO_DEPTH);
  assign fifo_empty_a = (fifo_count_a == 0);
  assign fifo_empty_b = (fifo_count_b == 0);

  logic any_outstanding;
  assign any_outstanding = ((fifo_count_a != 0) || (fifo_count_b != 0));
  
  logic can_issue_a, can_issue_b;
  assign can_issue_a = (vlsif.enable && vlsif.op == 7'b0100111 && !fifo_full_a);
  assign can_issue_b = (vlsif.enable && vlsif.op == 7'b0100111 && !fifo_full_b); 

  typedef enum logic [1:0] { IDLE, DATA } state_t;
  state_t state, next_state;

  // Registered command fields
  logic [7:0]  imm_a_r, imm_b_r;
  logic [3:0]  vd_a_r, vd_b_r;
  logic [4:0]  rs1_a_r, rs1_b_r;
  logic        row_col_a_r, row_col_b_r;
  logic [5:0]  num_rows_a_r, num_rows_b_r, num_cols_a_r, num_cols_b_r;
  logic        id_a_r, id_b_r;
  // logic [15:0] load_data_a_r, load_data_b_r;
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
      // load_data_a_r <= '0;
      // load_data_b_r <= '0;
      op_r <= '0;
      v2_a_r <= '0;
      v2_b_r <= '0;
      
      //FIFO Signals
      fifo_head_a <= '0;
      fifo_head_b <= '0;
      fifo_tail_a <= '0;
      fifo_tail_b <= '0;
      fifo_count_a <= '0;
      fifo_count_b <= '0;
    end 
    else begin
    
      state <= next_state;

      if(can_issue_a) begin
        fifo_mem_a[fifo_tail_a] <= vlsif.vd_a;
        fifo_tail_a <= fifo_tail_a + 1'b1;
        fifo_count_a <= fifo_count_a + 1'b1;
      end
      
      if(can_issue_b) begin
        fifo_mem_b[fifo_tail_b] <= vlsif.vd_b;
        fifo_tail_b <= fifo_tail_b + 1'b1;
        fifo_count_b <= fifo_count_b + 1'b1;
      end

      if (state == DATA && vlsif.dhit) begin
        if (!fifo_empty_a) begin
          fifo_head_a <= fifo_head_a + 1'b1;
          fifo_count_a <= fifo_count_a - 1'b1;
        end
        if (!fifo_empty_b) begin
          fifo_head_b <= fifo_head_b + 1'b1;
          fifo_count_b <= fifo_count_b - 1'b1;
        end
      end

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
      // if (state == DATA && vlsif.dhit) begin
        // load_data_a_r <= vlsif.load_data_a;
        // load_data_b_r <= vlsif.load_data_b;
    end
  end

  always_comb begin
    
    // Default Outputs
    vlsif.sp_store_data_a = '0;
    vlsif.sp_store_data_b = '0;
    // vlsif.sp_load_data_a  = '0;
    // vlsif.sp_load_data_b  = '0;
    
    // Writeback Destinations For Load
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

    // Address Calculation
    addr_a_n = {8'b0, vlsif.rs1_a} + {8'b0, vlsif.imm_a};
    addr_b_n = {8'b0, vlsif.rs1_b} + {8'b0, vlsif.imm_b};
    
    vlsif.sp_addr_a = addr_a_n;
    vlsif.sp_addr_b = addr_b_n;

    // if (state = DATA && vlsif.op == STORE && vlsif.dhit) begin
    //   vlsif.sp_store_data_a = sp_store_data_a;
    //   vlsif.sp_store_data_b = sp_store_data_b;
    // end

    if (state == DATA && vlsif.dhit) begin
      if (!fifo_empty_a) begin
        vlsif.wb_vd_a = fifo_mem_a[fifo_head_a];
      end
      if (!fifo_empty_b) begin
        vlsif.wb_vd_b = fifo_mem_b[fifo_head_b];
      end
    end

    case (state)
      IDLE: begin
        if (vlsif.enable) begin
          if (vlsif.op == 7'b0100111 || vlsif.op == 7'b0101000) begin //temp for now where 7'0100111 == load, 7'b0101000 == store
            next_state = DATA;
          end
        end
      end

      DATA: begin
        if (!any_outstanding && !(vlsif.enable && (vlsif.op == 7'b0100111 || vlsif.op == 7'b0101000))) begin
          next_state = IDLE;
          // vlsif.sp_load_data_a = load_data_a_r;
          // vlsif.sp_load_data_b = load_data_b_r;
        end
      end
    endcase
  end
endmodule
