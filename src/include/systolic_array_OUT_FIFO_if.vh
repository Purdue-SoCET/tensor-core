`ifndef SYSTOLIC_ARRAY_OUT_FIFO_IF_VH
`define SYSTOLIC_ARRAY_OUT_FIFO_IF_VH

interface systolic_array_OUT_FIFO_if #(parameter array_dim = 4, parameter data_w = 16);
  // Parameters
  // parameter array_dim = 4;    //4x4 systolic array
  // parameter data_w = 16;      //FP 16 for our implementation

  // Signals
  logic shift;    // FIFO shift signal
  logic [data_w-1:0] shift_value;   // next value to push out
  logic [data_w*array_dim-1:0] out;           // Final array_dim value to be seen by array
  // Memory Ports
  modport OUT_FIFO(
    input  shift, shift_value, 
    output out
  );
endinterface

`endif
