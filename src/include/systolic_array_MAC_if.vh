`ifndef SYSTOLIC_ARRAY_MAC_IF_VH
`define SYSTOLIC_ARRAY_MAC_IF_VH

interface systolic_array_MAC_if #(parameter data_w = 16, parameter mul_len = 2, parameter add_len = 3);
  // Parameters
  // parameter data_w = 16;      //FP 16 for our implementation
  // parameter MUL_LEN = 2,     // how long in cycles the mutliplication takes
  //  parameter ADD_LEN = 3     // how long in cycles the addition takes

  // Signals
  /* verilator lint_off UNUSEDSIGNAL */
  logic start;          // MAC unit start signal
  /* verilator lint_off UNUSEDSIGNAL */
  /* verilator lint_off UNUSEDSIGNAL */
  logic [$clog2(mul_len+add_len)-1:0]count;     // Count for Mulitplier to execute correct number of cycles
  /* verilator lint_off UNUSEDSIGNAL */
  logic [data_w-1:0] weight;                    // Input weight value to be pre-loaded
  logic [data_w-1:0] in_value;                  // Input value to be multiplied
  logic MAC_shift;                              // shift the input to the next array
  logic [data_w-1:0] in_pass;                  // Input value to be passed to next MAC
  logic [data_w-1:0] in_accumulate;             // Input accumulate value from above
  logic [data_w-1:0] out_accumulate;            // Output accumulate value

  // MAC Port for Array
  modport MAC(
    input  start, count, weight, in_value, MAC_shift, in_accumulate,
    output out_accumulate, in_pass
  );
endinterface

`endif
