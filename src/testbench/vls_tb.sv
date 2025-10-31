`include "vls_if.vh"
`include "vector_if.vh"
`include "vector_types.vh"

`timescale 1 ns / 1 ns

module vls_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST = 1;

    always #(PERIOD/2) CLK++;

    vls_if vlsif ();
    vls DUT (.CLK(CLK), .nRST(nRST), .vlsif(vlsif));

    int casenum;
    string casename;

initial begin
    casenum = '0;
    casename = "nRST";

    nRST = '0;

    #(PERIOD);

    nRST = 1;

    casenum = 0;
    casename = "ASYNC Reset ";

    vlsif.valid = '0;
    // vlsif.dhit = '0;
    vlsif.imm_a = '0;
    vlsif.imm_b = '0;
    vlsif.vd_a = '0;
    vlsif.vd_b = '0;
    vlsif.rs1_a = '0;
    vlsif.rs1_b = '0;
    vlsif.row_col_a = '0; 
    vlsif.row_col_b = '0;
    vlsif.num_rows_a = '0;
    vlsif.num_rows_b = '0;
    vlsif.num_cols_a = '0;
    vlsif.num_cols_b = '0;
    vlsif.id_a = '0; 
    vlsif.id_b = '0;
    foreach (vlsif.load_data_a[i]) vlsif.load_data_a[i] = '0;
    foreach (vlsif.load_data_b[i]) vlsif.load_data_b[i] = '0;
    vlsif.op = '0;
    vlsif.v2_a = '0;
    vlsif.v2_b = '0;
    vlsif.vec_res = '0;
    vlsif.ready_in = '0;
    
    #(PERIOD * 5);

    casenum = 1;
    casename = "DATA";
    
    vlsif.valid = 1;
    vlsif.vec_res = 1;
    vlsif.op = 7'b0100111;

    #(PERIOD * 5);

    ///////////////////////////////////////////////////////////////

    casenum = 2;
    casename = "STORE";

    vlsif.valid = '1;
    // vlsif.dhit = '0;
    vlsif.imm_a = 32'd10;
    vlsif.imm_b = 32'd15;
    vlsif.vd_a = '0;
    vlsif.vd_b = '0;
    vlsif.rs1_a = 32'd50;
    vlsif.rs1_b = 32'd50;
    vlsif.row_col_a = 1; 
    vlsif.row_col_b = 1;
    vlsif.num_rows_a = 5'b1;
    vlsif.num_rows_b = 5'b1;
    vlsif.num_cols_a = 5'b1;
    vlsif.num_cols_b = 5'b1;
    vlsif.id_a = 1; 
    vlsif.id_b = 0;
    foreach (vlsif.load_data_a[i]) vlsif.load_data_a[i] = '0;
    foreach (vlsif.load_data_b[i]) vlsif.load_data_b[i] = '0;
    vlsif.op = 7'b0101000;
    vlsif.v2_a = 4'b1;
    vlsif.v2_b = 4'b01;
    vlsif.vec_res = 0;
    vlsif.ready_in = 1;

    #(PERIOD * 5);
    
    ///////////////////////////////////////////////////////////////

    casenum = 3;
    casename = "LOAD";

    vlsif.valid = '1;
    // vlsif.dhit = '0;
    vlsif.imm_a = 32'd10;
    vlsif.imm_b = 32'd15;
    vlsif.vd_a = 4'b001;
    vlsif.vd_b = 4'b010;
    vlsif.rs1_a = 32'd50;
    vlsif.rs1_b = 32'd50;
    vlsif.row_col_a = 1; 
    vlsif.row_col_b = 1;
    vlsif.num_rows_a = 5'b1;
    vlsif.num_rows_b = 5'b1;
    vlsif.num_cols_a = 5'b1;
    vlsif.num_cols_b = 5'b1;
    vlsif.id_a = 1; 
    vlsif.id_b = 0;
    foreach (vlsif.load_data_a[i]) vlsif.load_data_a[i] = 32'd10;
    foreach (vlsif.load_data_b[i]) vlsif.load_data_b[i] = 32'd10;
    vlsif.op = 7'b0101000;
    vlsif.v2_a = '0;
    vlsif.v2_b = '0;
    vlsif.vec_res = 0;
    vlsif.ready_in = 1;
    
    ///////////////////////////////////////////////////////////////

    casenum = 4;
    casename = "Pop VD From Queue";

    vlsif.valid = '1;
    // vlsif.dhit = '0;
    vlsif.imm_a = 32'd10;
    vlsif.imm_b = 32'd15;
    vlsif.vd_a = 4'b001;
    vlsif.vd_b = 4'b010;
    vlsif.rs1_a = 32'd50;
    vlsif.rs1_b = 32'd50;
    vlsif.row_col_a = 1; 
    vlsif.row_col_b = 1;
    vlsif.num_rows_a = 5'b1;
    vlsif.num_rows_b = 5'b1;
    vlsif.num_cols_a = 5'b1;
    vlsif.num_cols_b = 5'b1;
    vlsif.id_a = 1; 
    vlsif.id_b = 0;
    vlsif.op = 7'b0101000;
    vlsif.v2_a = '0;
    vlsif.v2_b = '0;
    vlsif.ready_in = 1;
    
    #(PERIOD * 8);

    foreach (vlsif.load_data_a[i]) vlsif.load_data_a[i] = 32'd10;
    foreach (vlsif.load_data_b[i]) vlsif.load_data_b[i] = 32'd10;

    vlsif.vec_res = 1;
    
    #(PERIOD * 10);

    $stop;
end
endmodule