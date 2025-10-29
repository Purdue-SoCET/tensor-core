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

    // Other Parameters
    parameter NUM_ELEMENTS = 32;
    parameter ESZ = 16; // Element Size
    parameter ESZ_W = $clog2(ESZ);

    // VEGGIE Params
    parameter READ_PORTS = 4;
    parameter WRITE_PORTS = 4;
    parameter MASK_PORTS = 2;
    parameter NUM_MASKS = 16; // Total maskss
    parameter MASK_BANK_COUNT=2;
    parameter MASK_IDX = $clog2(NUM_MASKS);

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

    typedef logic [SLICE_ID_W-1:0] slice_idx_t;
    typedef logic [LANE_ID_W-1:0] lane_id_t;
    typedef logic [VL_W-1:0] vl_t;

    typedef logic [$clog2(NUM_MASKS)-1:0] mask_sel_t;
    typedef logic [VLMAX-1:0]              vmask_t;

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
        VALU_SUB       = 6'h01
    } valu_op_t;

    // TOP LEVEL CONTROL SIGNALS
    typedef struct packed {
        logic wen; // write en
        vsel_t vwsel; // vector write select 
        logic [2:0] valid; // valid FU
        logic [4:0] vop; // Vector op for ALU
        dtype_t datatype; // FP16, INT32, ETC
        logic vm; 
        logic rm;
        logic[1:0] sp;
        logic swizzle;
        logic memtovreg;
        logic sp_write;
        logic sp_read;
        vl_t vl;
        logic[4:0] shift; // TBD
    } control_t;

    // Veggie Input Signals
    
    typedef struct packed {
        // VDATA Writes
        vsel_t[WRITE_PORTS-1:0] vd;
        vreg_t[WRITE_PORTS-1:0] vdata;
        logic[WRITE_PORTS-1:0] WEN;
        // VDATA Reads
        vsel_t[READ_PORTS-1:0] vs;
        logic[READ_PORTS-1:0] REN;
        // MASK Reads/Writes
        mask_sel_t[MASK_BANK_COUNT-1:0] vmd; 
        vmask_t[MASK_BANK_COUNT-1:0] mvdata;
        logic[MASK_BANK_COUNT-1:0] MWEN; // mask enable
        // VMASK Reads
        mask_sel_t[MASK_BANK_COUNT-1:0] vms;
        logic[MASK_BANK_COUNT-1:0] MREN; // mask enable
    } veggie_in_t;
    /*
    typedef struct packed {
        vsel_t      [WRITE_PORTS-1:0]       vd;
        vreg_t      [WRITE_PORTS-1:0]       vdata;
        logic       [WRITE_PORTS-1:0]       WEN;

        vsel_t      [READ_PORTS-1:0]        vs;
        logic       [READ_PORTS-1:0]        REN;            // <-- had missing :0

        mask_sel_t  [MREAD_PORTS-1:0]       vms;            // <-- was scalar, needs per-port
        mask_sel_t  [MWRITE_PORTS-1:0]      vmd;            // <-- was scalar, needs per-port
        logic       [MREAD_PORTS-1:0]       MREN;           // <-- size by MREAD_PORTS
        logic       [MWRITE_PORTS-1:0]      MWEN;           // <-- size by MWRITE_PORTS
        logic       [MWRITE_PORTS-1:0][VLMAX-1:0] mvdata;   // 32-bit (1b x 32 elems) per mask write port
    } veggie_in_t;
    */

    typedef struct packed {
        vreg_t[READ_PORTS-1:0] vreg;
        logic [READ_PORTS-1:0] dvalid;
        vmask_t[MASK_PORTS-1:0] vmask;
        logic [MASK_PORTS-1:0] mvalid;
        logic ready; // to SB
    } veggie_out_t;

    typedef struct packed {
        vreg_t[READ_PORTS-1:0] vreg;
        vmask_t[MASK_PORTS-1:0] vmask;
        logic [MASK_PORTS-1:0] ivalid; // ASSUMING NUM MASKS = INSTR BW
    } opbuff_out_t; 

    typedef struct {
        logic REN;
        logic WEN;
        logic[READ_PORTS-1:0] tag;
        vsel_t vs;
        vsel_t vd;
        vreg_t vdata;
    } bank_in_t;

    typedef struct {
        logic      MWEN;    // 1 bit
        logic      MREN;    // 1 bit
        mask_sel_t vmd;     // 3 bits (write row select, 0..7)
        mask_sel_t vms;     // 3 bits (read  row select, 0..7)
        vmask_t    mvdata;  // 32-bit mask write data
        logic[MASK_BANK_COUNT-1:0] tag;
    } mbank_in_t;


    typedef struct {
        logic valid;
        logic [ESZ*NUM_ELEMENTS-1:0] ddata;
    } bank_out_t;

    typedef struct {
        logic valid;
        logic [NUM_ELEMENTS-1:0] mdata;
    } mbank_out_t;

    typedef enum logic [1:0] {
        READY,
        CONFLICT
    } conflict_state_t;
    // --------------------------------------------------------------------------------

    // MaskU Structs -------------------------------------------------------------------
    typedef struct packed {
        logic vm;
        logic[NUM_ELEMENTS-1:0] vmask;
    } masku_in_t;

    // Output to 16 lanes
    typedef struct packed {
        logic[NUM_LANES-1:0][SLICE_W-1:0] mask; // 2 bits per lane to be hard wired
    } masku_out_t;

    // Lane Structs --------------------------------------------------------------------
    /*
    typedef enum logic [2:0] {
        ALLU = 3'b000,
        EXP  = 3'b001,
        SQRT = 3'b010,
        MUL  = 3'b011,
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
    */
endpackage
`endif
