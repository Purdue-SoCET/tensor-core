`ifndef FU_SCALAR_LS_IF_VH
`define FU_SCALAR_LS_IF_VH

`include "types_pkg.vh"
`include "cpu_types.vh"

interface fu_scalar_ls_if;

  // import types
  import types_pkg::*;
  import cpu_types::*;

  word_t imm, dmemload, dmemaddr, dmem_in, dmemstore, rs1, rs2;
  scalar_mem_t mem_type;
  logic dhit, dmemWEN, dmemREN, dhit_in;

  modport icache (
    
  );

  modport dcache (
    input dmemaddr, dmemREN, dmemWEN, dmemstore,
    output dhit_in, dmem_in
  );

  modport sls (
    input imm, mem_type, rs1, rs2, dmem_in, dhit_in,
    output dmemaddr, dmemREN, dmemWEN, dmemstore, dmemload, dhit
  );

  modport tb (
    input dmemaddr, dmemREN, dmemWEN, dmemstore, dmemload, dhit,
    output imm, mem_type, rs1, rs2, dmem_in, dhit_in
  );

endinterface
`endif //FU_SCALAR_IF_VH