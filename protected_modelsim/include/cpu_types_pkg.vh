/*
  Eric Villasenor
  evillase@gmail.com

  all types used to make life easier.

  Shubham Rastogi
  shubhamrastogi3111995@gmail.com

  Ansh Patel
  patelansh092@gmail.com

  cache structs added
  
*/
`ifndef CPU_TYPES_PKG_VH
`define CPU_TYPES_PKG_VH

package cpu_types_pkg;

  // word width and size
  parameter WORD_W    = 32;
  parameter WBYTES    = WORD_W/8;

  // instruction format widths
  parameter OP_W      = 7;

  parameter REG_W     = 5;
  parameter FUNC7_W    = OP_W;
  parameter FUNC3_W    = 3;
  parameter IMM_W_I    = 12;
  parameter IMM_W_U_J  = 20;

  // alu op width
  parameter AOP_W     = 4;

  // icache format widths
  parameter ITAG_W    = 26;
  parameter IIDX_W    = 4;
  parameter IBLK_W    = 0; // <- important
  parameter IBYT_W    = 2;

  // dcache format widths
  parameter DTAG_W    = 26;
  parameter DIDX_W    = 3;
  parameter DBLK_W    = 1;
  parameter DBYT_W    = 2;
  parameter DWAY_ASS  = 2;

// opcodes
  // opcode type
  typedef enum logic [OP_W-1:0] {
    RTYPE     = 7'b0110011,
    ITYPE     = 7'b0010011,
    ITYPE_LW  = 7'b0000011,
    JALR      = 7'b1100111,
    STYPE     = 7'b0100011,
    BTYPE     = 7'b1100011,
    JAL       = 7'b1101111,
    LUI       = 7'b0110111,
    AUIPC     = 7'b0010111,
    LR_SC     = 7'b0101111,
    HALT      = 7'b1111111
  } opcode_t;

  typedef enum logic[4:0] {
    LR = 5'h02,
    SC = 5'h03
  } funct5_atomic_t;
  
  // r/itype funct3 op type
  typedef enum logic [FUNC3_W-1:0] {
    SLL     = 3'h1,
    SRL_SRA = 3'h5,
    ADD_SUB = 3'h0,
    AND     = 3'h7,
    OR      = 3'h6,
    XOR     = 3'h4,
    SLT     = 3'h2,
    SLTU    = 3'h3
  } funct3_r_t;

  typedef enum logic [FUNC3_W-1:0] {
    ADDI    = 3'h0,
    XORI    = 3'h4,
    ORI     = 3'h6,
    ANDI    = 3'h7,
    SLLI    = 3'h1,
    SRLI_SRAI = 3'h5,
    SLTI    = 3'h2,
    SLTIU   = 3'h3
  } funct3_i_t;

  typedef enum logic [FUNC3_W-1:0] {
    LB      = 3'h0,
    LH      = 3'h1,
    LW      = 3'h2,
    LBU     = 3'h4,
    LHU     = 3'h5
  } funct3_ld_i_t;

  typedef enum logic [FUNC3_W-1:0] {
    SB      = 3'h0,
    SH      = 3'h1,
    SW      = 3'h2
  } funct3_s_t;

  typedef enum logic [FUNC3_W-1:0] {
    BEQ     = 3'h0,
    BNE     = 3'h1,
    BLT     = 3'h4,
    BGE     = 3'h5,
    BLTU    = 3'h6,
    BGEU    = 3'h7
  } funct3_b_t;

  // rtype funct7 op type
  typedef enum logic [FUNC7_W-1:0] {
    ADD     = 7'h00,
    SUB     = 7'h20
  } funct7_r_t;

  // rtype sra,srl funct7 op type
  typedef enum logic [FUNC7_W-1:0] {
    SRA     = 7'h20,
    SRL     = 7'h00
  } funct7_srla_r_t;

  // alu op type
  typedef enum logic [AOP_W-1:0] {
    ALU_SLL     = 4'b0000,
    ALU_SRL     = 4'b0001,
    ALU_SRA     = 4'b0010,
    ALU_ADD     = 4'b0011,
    ALU_SUB     = 4'b0100,
    ALU_AND     = 4'b0101,
    ALU_OR      = 4'b0110,
    ALU_XOR     = 4'b0111,
    ALU_SLT     = 4'b1010,
    ALU_SLTU    = 4'b1011
  } aluop_t;

// instruction format types
  // register bits types
  typedef logic [REG_W-1:0] regbits_t;

  // j type
  typedef struct packed {
    logic [IMM_W_U_J-1:0] imm;
    regbits_t             rd;
    opcode_t              opcode;
  } j_t;

  // u type
  typedef struct packed {
    logic [IMM_W_U_J-1:0] imm;
    regbits_t             rd;
    opcode_t              opcode;
  } u_t;

  // b type
  typedef struct packed {
    logic [7-1:0]       imm2;
    regbits_t           rs2;
    regbits_t           rs1;
    funct3_b_t          funct3;
    logic [5-1:0]       imm1;
    opcode_t            opcode;
  } b_t;

  // s type
  typedef struct packed {
    logic [7-1:0]       imm2;
    regbits_t           rs2;
    regbits_t           rs1;
    funct3_s_t          funct3;
    logic [5-1:0]       imm1;
    opcode_t            opcode;
  } s_t;

  // i type
  typedef struct packed {
    logic [IMM_W_I-1:0] imm;
    regbits_t           rs1;
    funct3_i_t          funct3;
    regbits_t           rd;
    opcode_t            opcode;
  } i_t;

  // r type
  typedef struct packed {
    funct7_r_t          funct7;
    regbits_t           rs2;
    regbits_t           rs1;
    funct3_r_t          funct3;
    regbits_t           rd;
    opcode_t            opcode;
  } r_t;

// cache address format types
  // icache format type
  typedef struct packed {
    logic [ITAG_W-1:0]  tag;
    
    logic [IIDX_W-1:0]  idx;
    logic [IBYT_W-1:0]  bytoff;
  } icachef_t;

  // dcache format type
  typedef struct packed {
    logic [DTAG_W-1:0]  tag;
    logic [DIDX_W-1:0]  idx;
    logic [DBLK_W-1:0]  blkoff;
    logic [DBYT_W-1:0]  bytoff;
  } dcachef_t;

// word_t
  typedef logic [WORD_W-1:0] word_t;

// memory state
  // ramstate
  typedef enum logic [1:0] {
    FREE,
    BUSY,
    ACCESS,
    ERROR
  } ramstate_t;

// cache frame structs
  //dcache frame
  typedef struct packed {
	logic valid;
	logic dirty;
	logic [DTAG_W - 1:0] tag;
	word_t [1:0] data;
  } dcache_frame;

  //icache frame  
  typedef struct packed {
	logic valid;
	logic [ITAG_W - 1:0] tag;
	word_t data;
  } icache_frame;

endpackage
`endif //CPU_TYPES_PKG_VH
