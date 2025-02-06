`ifndef FUST_G_IF_VH
`define FUST_G_IF_VH
`include "datapath_types.vh"

interface fust_g_if;
  import datapath_pkg::*;

  // Inputs from dispatch
  logic en;
  //logic fu; //dont need op idx with 1 row in FUST
  fust_g_row_t fust_row;

  // Outputs of stage
  fust_g_t fust;
    
  modport FUSTG (
      input en, fust_row,
      output fust
  );

endinterface
`endif
