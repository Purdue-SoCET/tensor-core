/* PIPELINE TYPES INTERFACE */

`ifndef PIPELINE_PKG_VH
`define PIPELINE_PKG_VH
`include "isa_types.vh"

package pipeline_pkg;
    import isa_pkg::*;

// FETCH/DISPATCH LATCH:
    typedef struct packed
    {
        word_t instr, pc;
    }   fd_t;

// ISSUE/EXECUTE LATCH:
    typedef struct packed
    {
        word_t instr, rdat1, rdat2, pc;
        logic out, fust_s, fust_m, fust_g;
    }   ie_t;

//  EXECUTE/WRITEBACK LATCH:
    typedef struct packed
    {
        word_t wb_data;
    }   ew_t;

endpackage;
`endif