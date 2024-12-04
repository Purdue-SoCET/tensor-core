`ifndef SYSTOLIC_ARRAY_MAC_IF_VH
`define SYSTOLIC_ARRAY_MAC_IF_VH

interface systolic_array_MAC_if #(parameter data_w = 16);
  // Parameters
  // parameter data_w = 16;      //FP 16 for our implementation

  // Signals
  logic start;          // MAC unit start signal
  logic count;          // Count for Mulitplier to execute correct number of cycles
  logic [data_w-1:0] weight;            // Input weight value to be pre-loaded
  logic [data_w-1:0] in_value;          // Input value to be multiplied
  logic [data_w-1:0] in_accumulate;     // Input accumulate value from above
  logic [data_w-1:0] out_accumulate;    // Output accumulate value

  // MAC Port for Array
  modport MAC(
    input  start, count, weight, in_value, in_accumulate,
    output out_accumulate
  );
endinterface

`endif