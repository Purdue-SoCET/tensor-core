`include "vector_types.vh"
`include "vector_if.vh"
`include "vls_if.vh"
//need to add a control signal for the subtract module to flip the sign of the second input
module vaddsub(
    input logic CLK, 
    input logic nRST,
    vls_if.vls vlsif 
);

// importing vector types package
import vector_pkg::*;

//defining states
typedef enum logic [1:0] {
    IDLE = 1'b0;
    DATA = 1'b1;
} state_t;

state_t state, next_state; //defining current and next states

logic [7:0] imm_a_r, imm_b_r;
logic [3:0] vd_a_r, vd_b_r;
logic [4:0] rs1_a_r, rs1_b_r;
logic row_col_a_r, row_col_b_r;
logic [5:0] num_rows_a_r, num_rows_b_r, num_cols_a_r, num_cols_b_r;
logic id_a_r, id_b_r;
logic [15:0] load_data_a_r, load_data_b_r;
logic [6:0] op_r;
logic [3:0] v2_a_r, v2_b_r;


always_ff @(posedge CLK, negedge nRST) begin
    if (!nRST) begin
        state <= IDLE;
        imm_a_r <= '0;
        imm_b_r <= '0;
        vd_a_r <= '0;
        vd_b_r <= '0;
        rs1_a_r <= '0;
        rs1_b_r <= '0;
        row_col_a_r <= '0;
        row_col_b_r <= '0;
        num_rows_a_r <= '0;
        num_rows_b_r <= '0;
        num_cols_a_r <= '0;
        num_cols_b_r <= '0;
        logic id_a_r <= '0;
        id_b_r <= '0;
        load_data_a_r <= '0;
        load_data_b_r <= '0;
        op_r <= '0;
        v2_a_r <= '0;
        v2_b_r <= '0;
        
    end
    else begin
        state <= next_state;
        imm_a_r <= vlsif.imm_a;
        imm_b_r <= vlsif.imm_b;
        vd_a_r <= vlsif.vd_a;
        vd_b_r <= vlsif.vd
        rs1_a_r <= vlsif.rs1_a;
        rs1_b_r <= vlsif.rs1_b;
        row_col_a_r <= vlsif.row_col_a;
        row_col_b_r <= vlsif.row_col_b;
        num_rows_a_r <= vlsif.num_rows_a;
        num_rows_b_r <= vlsif.num_rows_b;
        num_cols_a_r <= vlsif.num_cols_a;
        num_cols_b_r <= vlsif.num_cols_b;
        logic id_a_r <= vlsif.id_a;
        id_b_r <= vlsif.id_b;
        load_data_a_r <= vlsif.load_data_a;
        load_data_b_r <= vlsif.load_data_b;
        op_r <= vlsif.op;
        v2_a_r <= vslif.v2_a;
        v2_b_r <= vlsif.v2_b;
        out <= next_out;
    end
end
    
    always_comb begin
        next_state = state;
        vlsif.sp_store_data_a = '0;
        vlsif.sp_store_data_b = '0;
        vslif.sp_load_data_a = '0;
        vslif.sp_load_data_b = '0;

        if (vslif.enable) begin
            casez (state) 
                IDLE: begin
                    if (vslif.op = STORE) begin
                        next_state = DATA;
                    end 
                    else if (vslif.op = LOAD) begin
                        next_state = DATA;
                    end
                    else begin
                        next_state = IDLE;
                    end
                end
                DATA: begin
                    if (vlsif.op == STORE) begin
                        vlsif.sp_op = op_r;
                        vslif.sp_row_col_a = row_col_a_r;
                        vslif.sp_row_col_b = row_col_b_r;
                        vslif.sp_nums_rows_a = num_rows_a_r;
                        vslif.sp_num_rows_b = num_rows_b_r;
                        vlsif.sp_num_cols_a = num_cols_a_r;
                        vlsif.sp_num_cols_b = num_cols_b_r;
                        vlsif.sp_id_a = id_a_r;
                        vlsif.sp_id_b = id_b_r;
                        vslif.sp_addr1_reg = imm_a_r + rs1_a_r;
                        vslif.sp_addr2_reg = imm_b_r + rs1_b_r;
                        if (sls_if.dhit) begin
                            next_state = IDLE;
                            vlsif.sp_store_data_a = v2_a_r;
                            vlsif.sp_store_data_b = v2_b_r;
                        end
                    end 
                    else if (vlsif.op = LOAD) begin
                        vlsif.sp_op = op_r;
                        vslif.sp_row_col_a = row_col_a_r;
                        vslif.sp_row_col_b = row_col_b_r;
                        vslif.sp_nums_rows_a = num_rows_a_r;
                        vslif.sp_num_rows_b = num_rows_b_r;
                        vlsif.sp_num_cols_a = num_cols_a_r;
                        vlsif.sp_num_cols_b = num_cols_b_r;
                        vlsif.sp_id_a = id_a_r;
                        vlsif.sp_id_b = id_b_r;
                        vslif.sp_addr1_reg = imm_a_r + rs1_a_r;
                        vslif.sp_addr2_reg = imm_b_r + rs1_b_r;
                        if (sls_if.dhit) begin
                            next_state = IDLE;
                            vlsif.sp_load_data_a = load_data_a_r;
                            vlsif.sp_load_data_b = load_data_b_r;
                        end
                    end
                end
            endcase
        end
    end


endmodule