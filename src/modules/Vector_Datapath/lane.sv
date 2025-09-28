// Vector Lane Module ============================================
// Author: Joseph Ghanem
// Email: jghanem@purdue.edu
// Vector Lane
// Issue Length = 1
// Commit Length = 1
    typedef struct packed {
        logic vm; // vector mask en
        logic rm;
        logic flush; // Needed?
        slice_t v1;
        slice_t v2; // If imm, will be broadcasted. Better to do while generating mask?
        vsel_t vd;
        slice_t vmask;
        opcode_t vop;
        lane_id_t lane_id;
        vl_t vl; 
    } lane_in_t;

// ========================================================================
`include "vector_if.vh"
`include "vector_types.vh"

module lane #(
)(
    input logic CLK, nRST,
    vector_if.lane lif
); 
    import vector_pkg::*;
    
    logic alu_valid, exp_valid, sqrt_valid, mul_valid, div_valid;
    slice_t alu_iter, exp_iter, sqrt_iter, mul_iter, div_iter;
    vl_t alu_global_idx, exp_global_idx, sqrt_global_idx, mul_global_idx, div_global_idx;

    // Pipeline Interface Instantiation
    vector_if.sequence_alu seq_alu ();
    vector_if.alu_wb alu_wb ();

    // ALU Sequence Stage
    assign alu_valid = ((alu_global_idx < lif.lane_in.vl) || (lif.lane_in.vm && lif.lane_in.vmask[alu_iter]));
    assign alu_iter = (salu.alu_iter_o) ? salu.alu_iter_o + 1: `0;
    assign alu_global_idx = lif.lane_in.global_idx + alu_iter;

    // Lane ALU Execute stage
    sequence_ex alu (
        iter, valid, global_idx, alu_in
    );

    alu alu (CLK, nRST, alu_in);
    assign alu_ready = (salu.alu_iter_o == SLICE_W-1);
    assign lif.lane_out.reduction = (lif.lane_in.rm && alu_ready) ? alu.reduction : 0;

    // to WB arbiter
    // send ready, iter, gloval_idx, vd, result

    // WB Arbiter
    

    /*
    counter_exp
    pipeline_exp
    exp
    pipeline_exp_wb

    counter_sqrt
    pipeline_sqrt
    sqrt
    pipeline_sqrt_wb

    counter_mul
    pipeline_mul
    mul
    pipeline_mul_wb

    counter_div
    pipeline_div
    div
    pipeline_div_wb

    wb_arbiter inpute GVLS
    */
    
endmodule