`ifndef VDIV_IF_VH
`define VDIV_IF_VH

interface vdiv_if #(
  parameter int EXP_WIDTH = 5,
  parameter int MANT_WIDTH = 10
);

  localparam int WIDTH = EXP_WIDTH + MANT_WIDTH;

  typedef struct packed {
    logic valid_in, ready_out;
    logic [WIDTH:0] operand1;
    logic [WIDTH:0] operand2;
  } vdiv_in_t;

  typedef struct packed {
    logic valid_out, ready_in;
    logic [WIDTH:0] result;
  } vdiv_out_t;

  vdiv_in_t  in;
  vdiv_out_t out;

  modport div (
    input  in,
    output out
  );

  modport tb (
    input  out,
    output in
  );

endinterface

`endif
