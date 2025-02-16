/*
  Eric Villasenor
  evillase@gmail.com

  register file interface
*/
`ifndef REGISTER_FILE_IF_VH
`define REGISTER_FILE_IF_VH

// all types

interface register_file_if;
  // import types

  logic     WEN;
  logic [17:0] wsel, rsel1, rsel2;
  logic [31:0]    wdat, rdat1, rdat2;

  // register file ports
  modport rf (
    input   WEN, wsel, rsel1, rsel2, wdat,
    output  rdat1, rdat2
  );
  // register file tb
  modport tb (
    input   rdat1, rdat2,
    output  WEN, wsel, rsel1, rsel2, wdat
  );
endinterface

`endif //REGISTER_FILE_IF_VH