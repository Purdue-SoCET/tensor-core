`ifndef SQRT_IF_VH
`define SQRT_IF_VH
`include "vector_types.vh"

interface sqrt_if;
    import vector_pkg::*;

    fp16_t input_val;
    logic [15:0] output_val;
    logic valid_data_in, valid_data_out, ready;

    modport srif (
        input input_val, valid_data_in,
        output output_val, valid_data_out, ready
    );


endinterface

`endif