`ifndef FU_SCALAR_LS_IF_VH
`define FU_SCALAR_LS_IF_VH

`include "datapath_types.vh"

interface fu_scalar_ls_if;

  // import types
  import isa_pkg::*;
  import datapath_pkg::*;

  word_t imm, dmemload, dmemaddr, dmem_in, dmemstore, rs1, rs2;
  scalar_mem_t mem_type;
  logic dhit, dmemWEN, dmemREN, dhit_in;

  modport sls (
    input imm, mem_type, rs1, rs2, dmem_in, dhit_in,
    output dmemaddr, dmemREN, dmemWEN, dmemstore, dmemload, dhit
  );

  modport tb (
    input dmemaddr, dmemREN, dmemWEN, dmemstore, dmemload, dhit,
    output imm, mem_type, rs1, rs2, dmem_in, dhit_in
  );

  modport dcache (
    input dmemREN, dmemWEN, dmemstore, dmemaddr,
    output dmem_in, dhit_in
  );

endinterface
`endif //FU_SCALAR_IF_VH
