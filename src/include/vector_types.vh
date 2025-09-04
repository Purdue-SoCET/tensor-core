`ifndef VECTOR_PKG_VH
`define VECTOR_PKG_VH

package vector_pkg;

    parameter OPCODE_W = 7;
    parameter VIDX_W = 8;
    parameter RIDX_W = 8;
    parameter IMM_W = 8;
    parameter DTYPE_W = 2;
    parameter INSTR_W = 32;

    typedef logic [OPCODE_W-1:0] opcode_t;
    typedef logic [VIDX_W-1:0] vreg_t;
    typedef logic [RIDX_W-1:0] reg_t;
    typedef logic [IMM_W-1:0] imm_t;
    typedef logic [DTYPE_W-1:0] dtype_t;

    typedef struct packed {
        logic swizzle;
        logic transpose; // 0 = row, 1 = column
        dtype_t datatype;
        vreg_t vd; 
        logic mask;
        reg_t rs1; // base address
        logic sp; // scratchpad0, scratchpad1
        opcode_t opcode;
        logic [INSTR_W-DTYPE_W-VIDX_W-RIDX_W-OPCODE_W-5:0] reserve;  
    } rv_mtype_t;

    typedef struct packed {
        logic mask;
        vreg_t vd;
        vreg_t vs1;
        vreg_t vs2;
        opcode_t opcode;
    } rv_rtype_t;

    typedef struct packed {
        logic mask;
        vreg_t vd;
        vreg_t vs1;
        imm_t imm; 
        opcode_t opcode;
    } rv_itype_t;


endpackage
`endif
