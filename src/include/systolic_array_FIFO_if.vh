`ifndef SYSTOLIC_ARRAY_FIFO_IF_VH
`define SYSTOLIC_ARRAY_FIFO_IF_VH

interface systolic_array_FIFO_if #(parameter array_dim = 4, parameter data_w = 16);
  // Parameters
  // parameter array_dim = 4;    //4x4 systolic array
  // parameter data_w = 16;      //FP 16 for our implementation

  // Signals
  logic load;     // FIFO load signal
  logic shift;    // FIFO shift signal
  logic [data_w*array_dim-1:0] load_values;   // Load for a row of a matrix
  logic [data_w*array_dim-1:0] out;           // Final array_dim value to be seen by array
  // Memory Ports
  modport FIFO(
    input  load, shift, load_values, 
    output out
  );
endinterface

`endif
