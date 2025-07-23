`ifndef MAIN_MEM_IF_VH
`define MAIN_MEM_IF_VH
`include "isa_types.vh"
`include "datapath_types.vh"

interface main_mem_if;
  import isa_pkg::*;

  logic [3:0] write_en;
  word_t addr, data_in, data_out;
  logic busy, enable; 

  modport mem (
    input write_en, addr, data_in, enable,
    output data_out, busy
  );

endinterface

`endif
