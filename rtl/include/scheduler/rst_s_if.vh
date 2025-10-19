`ifndef RST_S_IF_VH
`define RST_S_IF_VH
`include "datapath_types.vh"

interface rst_s_if;
  import datapath_pkg::*;

  // Inputs from dispatch
  logic [4:0] di_sel;
  logic di_write;
  logic [1:0] di_tag;
  logic spec;
  logic flush;

  // Inputs from writeback
  logic [4:0] wb_sel;
  logic wb_write;
    
  // Outputs of stage
  rst_s_t status;
    
  modport RSTS (
      input di_sel, di_write, di_tag, wb_sel, wb_write, spec, flush,
      output status
  );

endinterface
`endif
