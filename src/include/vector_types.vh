`ifndef VECTOR_PKG_VH
`define VECTOR_PKG_VH

package vector_pkg;

    // Vector ISA ----------------------------------------------------------------------
    // LANE VARIABLES
    parameter NUM_LANES = 16;
    parameter LANE_ID_W = $clog2(NUM_LANES);
    parameter VLMAX = 32;

    parameter SLICE_W = VLMAX / NUM_LANES;
    parameter SLICE_ID_W = $clog2(SLICE_W);
    parameter VL_W = $clog2(VLMAX);

    // Instruction Fields
    parameter OPCODE_W = 7;
    parameter VIDX_W = 8;
    parameter RIDX_W = 8;
    parameter IMM_W = 8;
    parameter DTYPE_W = 2;
    parameter INSTR_W = 32;

    typedef logic [OPCODE_W-1:0] opcode_t;
    typedef logic [VIDX_W-1:0] vsel_t;
    typedef logic [RIDX_W-1:0] reg_t;
    typedef logic [IMM_W-1:0] imm_t;
    typedef logic [DTYPE_W-1:0] dtype_t;

    typedef logic [SLICE_ID_W-1:0] slice_t;
    typedef logic [LANE_ID_W-1:0] lane_id_t;
    typedef logic [VL_W-1:0] vl_t;

    typedef struct packed {
        logic swizzle;
        logic transpose; // 0 = row, 1 = column
        dtype_t datatype;
        vsel_t vd; 
        logic mask;
        reg_t rs1; // base address
        logic sp; // scratchpad0, scratchpad1
        opcode_t opcode;
        logic [INSTR_W-DTYPE_W-VIDX_W-RIDX_W-OPCODE_W-5:0] reserve;  
    } rv_mtype_t;

    typedef struct packed {
        logic mask;
        vsel_t vd;
        vsel_t vs1;
        vsel_t vs2;
        opcode_t opcode;
    } rv_rtype_t;

    typedef struct packed {
        logic mask;
        vsel_t vd;
        vsel_t vs1;
        imm_t imm; 
        opcode_t opcode;
    } rv_itype_t;
    // --------------------------------------------------------------------------------

    // Data Structures ----------------------------------------------------------------
   

    typedef struct packed {
        logic sign;
        logic [4:0] exp;
        logic [9:0] frac;
    } fp16_t; 

    typedef fp16_t [SLICE_W-1:0] slice_t;
    typedef fp16_t [VLMAX-1:0] vreg_t;

    typedef enum logic [5:0] {
        VALU_ADD       = 6'h00,
        VALU_SUB       = 6'h01,
    } valu_op_t;

    // TOP LEVEL CONTROL SIGNALS
    typedef struct packed {
        logic wen; // write en
        vsel_t vwsel; // vector write select 
        logic [1:0] valid; // valid FU
        logic [4:0] vop; // Vector op
        logic [1:0] valu_src; // VV, VS, VI
        dtype_t datatype; // FP16, INT32, ETC
        logic vm; 
        logic sp;
        logic swizzle;
        logic memtovreg;
        logic spwrite;
        logic spread;
    } control_t;

    // Veggie Input Signals
    typedef struct packed {
        logic WEN;
        vsel_t vd;
        vsel_t vs1;
        vsel_t vs2;
        logic vm;
        logic WEN;
    } veggie_in_t;

    typedef struct packed {
        vreg_t v1;
        vreg_t v2;
        vreg_t vmask;
        logic ready; // to SB
    } veggie_out_t;

    typedef struct packed {
        logic REN;
        logic WEN;
        logic tag;
        logic WEN;
        vsel_t vs;
        vsel_t vd;
        vreg_t vdata;
    } bank_in_t;

    typedef struct packed {
        logic vm;
        logic WEN;
        vsel_t vd;
        vreg_t vdata;
    } cntrl_bank_in_t;

    typedef enum logic [1:0] {
        IDLE,
        READ
    } conflict_state_t;

    typedef enum logic [1:0] {
        RW_CONFLICT = 2'b1x,
        RR_CONFLICT = 2'b01
    } conflict_type_t;
    // --------------------------------------------------------------------------------

    // Lane Structs --------------------------------------------------------------------
    typedef enum logic [2:0] {
        ALLU = 3'b000,
        EXP  = 3'b001,
        SQRT = 3'b010,
        MUL  = 3'b011
        DIV  = 3'b100
    } ready_t;

    typedef struct packed {
        logic vm; // vector mask en
        logic rm;
        logic flush; // Needed?
        slice_t v1;
        slice_t v2; // If imm, will be broadcasted. Better to do while generating mask?
        vsel_t vd;
        slice_t vmask;
        opcode_t vop;
        lane_id_t lane_id;
        vl_t global_idx;
        vl_t vl; 
    } lane_in_t;

    typedef struct packed {
        slice_t result;
        ready_t ready; // to SB
        fp16_t reduction; // TO rtree for rm mode
        lane_id_t lane_id;
        vsel_t vd;
    } lane_out_t;

endpackage
`endif
