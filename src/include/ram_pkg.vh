
`ifndef RAM_PKG_VH
`define RAM_PKG_VH

`include "isa_types.vh"

package ram_pkg;

  import isa_pkg::*;

// ramstate
  typedef enum logic [1:0] {
    FREE,
    BUSY,
    ACCESS,
    ERROR
  } ramstate_t;

endpackage

`endif