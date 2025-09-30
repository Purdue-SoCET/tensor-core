`ifndef VREDUCTION_ALU_IF_VH
`define VREDUCTION_ALU_IF_VH
`include "vector_types.vh"

typedef enum logic [1:0] {
    VR_MAX = 2'b00,
    VR_MIN = 2'b01,
    VR_SUM = 2'b10
} reduction_op;

interface vreduction_alu_if;
    import vector_pkg::*;

    fp16_t value_a, value_b, value_out;
    logic [1:0] alu_op;

    modport vralu (
        input value_a, value_b, alu_op,
        output value_out
    );
endinterface

`endif