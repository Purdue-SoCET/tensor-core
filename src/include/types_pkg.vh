`ifndef TYPES_PKG_VH
`define TYPES_PKG_VH

package types_pkg;
  // all our instruction params
  parameter WORD_W = 32;
  parameter REG_W  = 5;
  parameter MATRIX_W = 4;
  parameter VALUE_BITS = 16;
  parameter BITS_PER_ROW = MATRIX_W * VALUE_BITS;

  parameter FU_S_W = 2;
  parameter FU_M_W = 1;
  parameter MAT_S_W = 2;
  parameter ROW_S_W = 2;



  typedef logic [WORD_W-1:0] word_t;

  typedef logic [REG_W-1:0] regbits_t;
  typedef logic [MATRIX_W-1:0] mbits_t;

  typedef logic [FU_S_W-1:0] fu_sbits_t;
  typedef logic [FU_M_W-1:0] fu_mbits_t;
 
  // defines the Function Units
  typdef enum logic [FU_S_W-1:0] {
    ALU,
    LD_ST,
    BRANCH
  } fu_scalar;

  typdef enum logic [FU_M_W-1:0] {
    LD_ST,
    GEMM
  } fu_matrix;

  // Pipeline Stage Structs
  typedef struct packed {
    logic hazard;

    // control signals
    
  } dispatch_t;

  typedef struct packed {
    cu_t cu; 
  } issue_t;

  typedef struct packed {
    logic busy;
    regbits_t r;
    regbits_t r1;
    regbits_t r2;
    fu_sbits_t t1;
    fu_sbits_t t2;
  } fust_s_row_t;

  typedef struct packed {
    fust_s_row_t [FU_S_W-1:0] op;
  } fust_s_t;

  typedef struct packed {
    logic busy;
    mbits_t r;
    mbits_t r1;
    mbits_t r2;
    mbits_t r3;
    fu_mbits_t t1;
    fu_mbits_t t2;
    fu_mbits_t t3;
  } fust_m_row_t;

  typedef struct packed {
    fust_m_row_t [FU_M_W-1:0] op;
  } fust_m_t;

  typedef enum logic [2:0] {
    BEQ, 
    BNE, 
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
  } branch_t;

  typedef enum logic [1:0] {
    STORE,
    LOAD,
    MEM_TO_REG
  } scalar_mem_t; // 

  typedef enum logic [1:0] {
    STORE,
    LOAD
  } matrix_mem_t; // load or store for matrix ld_st fu

  typedef enum logic [2:0] {
    LOAD,
    ADD // not using it but here still 
  } utype_t;

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
    BEQ     = 3'h0,
    BNE     = 3'h1,
    BLT     = 3'h4,
    BGE     = 3'h5,
    BLTU    = 3'h6,
    BGEU    = 3'h7
  } funct3_b_t;

  typedef enum logic [FUNC7_W-1:0] {
    ADD     = 7'h00,
    SUB     = 7'h20
  } funct7_r_t;

  // rtype sra,srl funct7 op type
  typedef enum logic [FUNC7_W-1:0] {
    SRA     = 7'h20,
    SRL     = 7'h00
  } funct7_srla_r_t;

  typedef enum logic [FUNC7_W-1:0] {
    ADD     = 7'h00,
    SUB     = 7'h20
  } funct7_r_t;

  // rtype sra,srl funct7 op type
  typedef enum logic [FUNC7_W-1:0] {
    SRA     = 7'h20,
    SRL     = 7'h00
  } funct7_srla_r_t;
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


endpackage
`endif
