`include "cpu_types.vh"

interface writeback_if;
  import cpu_types::*;

  logic wb_select;
  word_t alu_out, store_out, wb_data;

  modport wb (
    input wb_select, alu_out, store_out,
    output wb_data
  );

  modport tb (
    input wb_data,
    output wb_select, alu_out, store_out
  );
endinterface