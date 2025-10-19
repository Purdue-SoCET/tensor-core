`ifndef FUST_M_IF_VH
`define FUST_M_IF_VH
`include "datapath_types.vh"

interface fust_m_if;
  import datapath_pkg::*;

  // Inputs from dispatch
  logic en;
  //logic fu; //dont need op idx with 1 row in FUST
  fust_m_row_t fust_row;

  // Inputs from issue
  logic busy;

  // Outputs of stage
  fust_m_t fust;
    
  modport FUSTM (
      input en, fust_row, busy,
      output fust
  );

endinterface
`endif
