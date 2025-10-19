`ifndef REGFILE_IF_VH
`define REGFILE_IF_VH

// all types
`include "datapath_types.vh"

interface regfile_if;
  // import types
  import isa_pkg::*;
  import datapath_pkg::*;

  logic     WEN;
  regbits_t wsel, rsel1, rsel2;
  word_t    wdata, rdat1, rdat2;

  // register file ports
  modport rf (
    input   WEN, wsel, rsel1, rsel2, wdata,
    output  rdat1, rdat2
  );
  // register file tb
  modport tb (
    input   rdat1, rdat2,
    output  WEN, wsel, rsel1, rsel2, wdata
  );
endinterface

`endif //REGISTER_FILE_IF_VH
