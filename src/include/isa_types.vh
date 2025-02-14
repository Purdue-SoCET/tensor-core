`ifndef ISA_PKG_VH
`define ISA_PKG_VH

package isa_pkg;
  // word width and size
  parameter WORD_W    = 32;
  parameter WBYTES    = WORD_W/8;

  // instruction format widths
  parameter OP_W      = 7;

  parameter REG_W     = 5;
  parameter MATRIX_W  = 4;
  parameter FUNC7_W   = OP_W;
  parameter FUNC3_W   = 3;
  parameter IMM_W_I   = 12;
  parameter IMM_W_U_J = 20;

  // alu op width
  parameter AOP_W     = 4;

  // Stride Parameter
  parameter stride    = 16;
  parameter SBYTES    = stride * 2;

  // word_t
  typedef logic [WORD_W-1:0] word_t;

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
    HALT      = 7'b1111111,
    LD_M      = 7'b1000011,
    ST_M      = 7'b1010011,
    GEMM      = 7'b1110011 
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
  typedef logic [REG_W-1:0]    regbits_t;
  typedef logic [MATRIX_W-1:0] matbits_t;

  // u type
  typedef enum logic [2:0] {
    UT_LOAD,
    UT_ADD // not using it but here still 
  } utype_t;

  typedef enum logic [2:0] {
    BT_BEQ, 
    BT_BNE, 
    BT_BLT,
    BT_BGE,
    BT_BLTU,
    BT_BGEU
  } branch_t;

endpackage
`endif
