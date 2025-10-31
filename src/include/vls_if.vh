`ifndef VLS_IF_VH
`define VLS_IF_VH
`include "vector_types.vh"
`include "vector_if.vh"

interface vls_if;
    import vector_pkg::*;

    //Inputs to Vector LS
    logic valid;
    logic dhit;
    logic [7:0] imm_a, imm_b;
    logic [3:0] vd_a, vd_b;
    logic [4:0] rs1_a, rs1_b;
    logic row_col_a, row_col_b;
    logic [5:0] num_rows_a, num_rows_b, num_cols_a, num_cols_b;
    logic id_a, id_b;
    logic [31:0] load_data_a [31:0], load_data_b [31:0];
    logic [6:0] op;
    logic [3:0] v2_a, v2_b;
    logic vec_res;
    logic ready_in;

    //Outputs from Vector LS
    logic [15:0] sp_store_data_a, sp_store_data_b;
    logic [6:0] sp_op;
    logic sp_row_col_a, sp_row_col_b;
    logic [5:0] sp_num_rows_a, sp_num_rows_b, sp_num_cols_a, sp_num_cols_b;
    logic sp_id_a, sp_id_b;
    logic [15:0] sp_addr_a, sp_addr_b;
    logic [31:0] [31:0] sp_load_data_a; 
    logic [31:0] [31:0] sp_load_data_b;
    logic [3:0] wb_vd_a, wb_vd_b;
    logic ready_out;


    modport vls (
    input valid, dhit, imm_a, imm_b, vd_a, vd_b, rs1_a, rs1_b, row_col_a, row_col_b, num_rows_a, num_rows_b, 
    num_cols_a, num_cols_b, id_a, id_b, load_data_a, load_data_b, op, v2_a, v2_b, vec_res, ready_in,
    
    output sp_store_data_a, sp_store_data_b, sp_op, sp_row_col_a, sp_row_col_b, sp_num_rows_a, sp_num_rows_b, 
    sp_num_cols_a, sp_num_cols_b, sp_id_a, sp_id_b, sp_addr_a, sp_addr_b, 
    sp_load_data_a, sp_load_data_b, wb_vd_a, wb_vd_b, ready_out
    );

    modport tb (
    input sp_store_data_a, sp_store_data_b, sp_op, sp_row_col_a, sp_row_col_b, sp_num_rows_a, sp_num_rows_b, 
    sp_num_cols_a, sp_num_cols_b, sp_id_a, sp_id_b, sp_addr_a, sp_addr_b, 
    sp_load_data_a, sp_load_data_b, wb_vd_a, wb_vd_b, ready_out,

    output valid, dhit, imm_a, imm_b, vd_a, vd_b, rs1_a, rs1_b, row_col_a, row_col_b, num_rows_a, num_rows_b, 
    num_cols_a, num_cols_b, id_a, id_b, load_data_a, load_data_b, op, v2_a, v2_b, vec_res, ready_in
    );

endinterface
`endif

