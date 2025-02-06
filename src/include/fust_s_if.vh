`ifndef FUST_S_IF_VH
`define FUST_S_IF_VH
`include "datapath_types.vh"

interface fust_s_if;
  import datapath_pkg::*;

  // Inputs from dispatch
  logic en;
  fu_scalar_t fu;
  fust_s_row_t fust_row;

  // Outputs of stage
  fust_s_t fust;
    
  modport FUSTS (
      input en, fu, fust_row,
      output fust
  );

endinterface
`endif
