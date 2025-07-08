`ifndef FUST_S_IF_VH
`define FUST_S_IF_VH
`include "datapath_types.vh"

interface fust_s_if;
  import datapath_pkg::*;

  // Inputs from dispatch
  logic en;
  fu_scalar_t fu;
  fust_s_row_t fust_row;
  logic [2:0][1:0] t1;
  logic [2:0][1:0] t2;
  logic flush;
  logic resolved;
  logic [2:0] busy;
  // fust_s_t fust;

  logic [2:0] out_busy;
  logic [2:0][1:0] out_t1;
  logic [2:0][1:0] out_t2;
  fust_s_row_t out_op_alu;
  fust_s_row_t out_op_sls;
  fust_s_row_t out_op_br;

  modport FUSTS (
      input en, fu, fust_row, busy, t1, t2, flush, resolved,
      output out_busy, out_t1, out_t2, out_op_alu, out_op_sls, out_op_br
  );

endinterface
`endif
