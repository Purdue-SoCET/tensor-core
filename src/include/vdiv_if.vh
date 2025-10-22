`ifndef VDIV_IF_VH
`define VDIV_IF_VH

interface vdiv_if;

  logic en, done;
  logic [15:0] a, b, result;

  modport div (
    input en, a, b,
    output result, done
  );

  modport tb (
    input result, done,
    output en, a, b
  );

endinterface

`endif
