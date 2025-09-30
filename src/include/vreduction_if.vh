`ifndef VREDUCTION_IF_VH
`define VREDUCTION_IF_VH

`include "vector_types.vh"
`include "vector_if.vh"



interface vreduction_if #(
    parameter LANES = 16
);
    import vector_pkg::*;

    fp16_t [LANES-1:0] vector_input;
    fp16_t [NUM_ELEMENTS-1:0] vector_output;
    logic [1:0] reduction_type;
    

`endif