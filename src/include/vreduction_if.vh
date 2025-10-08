`ifndef VREDUCTION_IF_VH
`define VREDUCTION_IF_VH

`include "vector_types.vh"



interface vreduction_if #(
    parameter LANES = 16
);
    import vector_pkg::*;

    fp16_t [LANES-1:0] lane_input;
    fp16_t [NUM_ELEMENTS-1:0] vector_input, vector_output;
    logic [1:0] reduction_type;
    logic input_valid, output_valid, clear, broadcast;
    logic [4:0] imm;
    
    modport ruif (
        input vector_input, lane_input, imm, reduction_type, clear, broadcast, input_valid, 
        output vector_output, output_valid
    );
endinterface

`endif