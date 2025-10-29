`ifndef RST_M_IF_VH
`define RST_M_IF_VH
`include "datapath_types.vh"

interface rst_m_if;
  import datapath_pkg::*;

  // Inputs from dispatch
  logic [3:0] di_sel;
  logic di_write;
  logic [1:0] di_tag;

  // Inputs from writeback
  logic [3:0] wb_sel;
  logic wb_write;
    
  // Outputs of stage
  rst_m_t status;
    
  modport RSTM (
      input di_sel, di_write, di_tag, wb_sel, wb_write,
      output status
  );

endinterface
`endif
