`ifndef ADDER_IF
`define ADDER_IF

interface adder_if #(parameter data_w = 16);
  // Parameters
  // parameter data_w = 16;      //FP 16 for our implementation

  // Signals.
  
  logic start;          // MAC unit start signal
  logic [data_w-1:0] in1;            // Input weight value to be pre-loaded
  logic [data_w-1:0] in2;          // Input value to be multiplied
  logic [data_w-1:0] result;     // Input accumulate value from above

  // MAC Port for Array
  modport adder(
    input  in1, in2, start,
    output result
  );
endinterface

`endif
