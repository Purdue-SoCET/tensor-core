// control unit

// need to include matrix related instructions, gemm, ld.m, sw.m

`include "datapath_types.vh"
`include "control_unit_if.vh"

module control_unit(
    control_unit_if.cu cu_if
);

    import isa_pkg::*;
    import datapath_pkg::*;

    word_t instr;
    logic [6:0] op;
    logic dummy;

    assign instr = cu_if.instr;
    assign op = opcode_t'(instr[6:0]);

    always_comb begin
      dummy = '0;
      cu_if.halt = '0;
      cu_if.i_flag = '0;
      cu_if.s_mem_type = scalar_mem_t'('0);
      cu_if.s_reg_write = '0;
      cu_if.m_reg_write = '0;
      cu_if.jalr = '0;
      cu_if.jal = '0;
      cu_if.u_type = utype_t'('0);
      cu_if.alu_op = aluop_t'('0);
      cu_if.branch_op = branch_t'('0);
      cu_if.imm = '0;
      cu_if.stride = '0;
      cu_if.fu_s = FU_NONE;
      cu_if.fu_m = fu_matrix_t'('0);
      cu_if.m_mem_type = matrix_mem_t'('0);
      cu_if.matrix_rd = '0;
      cu_if.matrix_rs1 = '0;
      cu_if.fu_t = FU_S_T;
      casez (op)
        RTYPE:
            begin 
                cu_if.s_reg_write = '1;
                cu_if.fu_s = FU_S_ALU;
                casez(instr[14:12])
                    SLL: cu_if.alu_op = ALU_SLL;
                    SRL_SRA: cu_if.alu_op = (instr[31:25] == 7'h20) ? ALU_SRA : ALU_SRL;
                    ADD_SUB: cu_if.alu_op = (instr[31:25] == 7'h20) ? ALU_SUB : ALU_ADD;
                    AND: cu_if.alu_op = ALU_AND;
                    OR: cu_if.alu_op = ALU_OR;
                    XOR: cu_if.alu_op = ALU_XOR;
                    SLT: cu_if.alu_op = ALU_SLT;
                    SLTU: cu_if.alu_op = ALU_SLTU;
                    default: cu_if.alu_op = aluop_t'('0);
                endcase
            end
        ITYPE: 
            begin 
                cu_if.s_reg_write = '1;
                cu_if.i_flag = '1;
                cu_if.imm = {{20{instr[31]}},instr[31:20]};
                cu_if.fu_s = FU_S_ALU;
                casez(instr[14:12])
                    ADDI: cu_if.alu_op = ALU_ADD;
                    XORI: cu_if.alu_op = ALU_XOR;
                    ORI: cu_if.alu_op = ALU_OR;
                    ANDI: cu_if.alu_op = ALU_AND;
                    SLLI: cu_if.alu_op = ALU_SLL;
                    SRLI_SRAI: cu_if.alu_op = (instr[31:25] == 7'h20) ? ALU_SRA : ALU_SRL;
                    SLTI: cu_if.alu_op = ALU_SLT;
                    SLTIU: cu_if.alu_op = ALU_SLTU;
                    default: cu_if.alu_op = aluop_t'('0);
                endcase
            end
        ITYPE_LW:
            begin
                if (instr[14:12] == funct3_i_t'(3'h2)) begin 
                    cu_if.imm = {{20{instr[31]}},instr[31:20]};   // $signed({instr[31:20]}); lowk kinda 
                    cu_if.s_reg_write = '1;
                    cu_if.i_flag = '1;
                    // cu_if.alu_op = ALU_ADD;
                    cu_if.s_mem_type = LOAD;
                    cu_if.fu_s = FU_S_LD_ST;
                end
            end
        JALR:
            begin 
                cu_if.imm = {{20{instr[31]}},instr[31:20]};
                cu_if.s_reg_write = '1;
                cu_if.jalr = '1;
                cu_if.alu_op = ALU_ADD;
                cu_if.i_flag = '1;
                cu_if.fu_s = FU_S_ALU;
            end
        STYPE:
            begin
                if (instr[14:12] == 3'h2) begin 
                    cu_if.imm = {{20{instr[31]}},instr[31:25],instr[11:7]};
                    cu_if.i_flag = '1;
                    // cu_if.alu_op = ALU_ADD
                    cu_if.s_mem_type = STORE;
                    cu_if.fu_s = FU_S_LD_ST;
                end 
            end
        BTYPE:
            begin 
                // cu_if.reg_write = '1;
                cu_if.imm = {{19{instr[31]}},instr[31],instr[7],instr[30:25],instr[11:8],1'b0};
                cu_if.fu_s = FU_S_BRANCH;
                casez(instr[14:12])
                    BEQ: 
                        begin 
                            cu_if.branch_op = BT_BEQ; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_op = 3'd1;
                        end
                    BNE: 
                        begin 
                            cu_if.branch_op = BT_BNE; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_op = 3'd2;
                        end
                    BLT: 
                        begin 
                            cu_if.branch_op = BT_BLT; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_op = 3'd3;
                        end
                    BGE: 
                        begin 
                            cu_if.branch_op = BT_BGE; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_op = 3'd4;
                        end
                    BLTU: 
                        begin 
                            cu_if.branch_op = BT_BLTU; 
                            // cu_if.alu_op = ALU_SLTU;
                            // cu_if.branch_op = 3'd5;
                        end
                    BGEU: 
                        begin 
                            cu_if.branch_op = BT_BGEU; 
                            // cu_if.alu_op = ALU_SLTU;
                            // cu_if.branch_op = 3'd6;
                        end
                    default: cu_if.branch_op = branch_t'('0);
                endcase
            end
        JAL:
            begin 
                cu_if.imm = {{11{instr[31]}},instr[31],instr[19:12],instr[20],instr[30:21],1'b0};
                cu_if.jal = '1;
                cu_if.s_reg_write = '1;
                cu_if.alu_op = ALU_ADD;
                cu_if.i_flag = '1;
                cu_if.fu_s = FU_S_ALU;
            end
        // LUI:
        //     begin
        //         cu_if.imm = {instr[31:12], 12'b0};
        //         cu_if.u_type = UT_LOAD;
        //         cu_if.s_reg_write = '1;
        //     end
        // AUIPC:
        //     begin 
        //         cu_if.u_type = ADD;
        //         cu_if.reg_write = '1;
        //         cu_if.imm = {instr[31:12], 12'b0};
        //     end
        HALT: cu_if.halt = '1;
        LD_M: 
            begin 
                cu_if.imm = {{22{instr[17]}}, instr[16:7]};
                // cu_if.i_flag = '1;
                // cu_if.alu_op = ALU_ADD;
                cu_if.stride = instr[22:18]; // register
                cu_if.fu_m = FU_M_LD_ST;
                cu_if.m_mem_type = M_LOAD;
                cu_if.matrix_rd = instr[31:28];
                cu_if.m_reg_write = '1;
                cu_if.fu_t = FU_M_T;
            end
        ST_M: //st.m
            begin
                cu_if.imm = {{22{instr[17]}}, instr[16:7]};
                cu_if.stride = instr[22:18]; // register
                cu_if.fu_m = FU_M_LD_ST;
                cu_if.m_mem_type = M_STORE;
                cu_if.matrix_rd = instr[31:28];
                cu_if.fu_t = FU_M_T;
            end
        GEMM: // gemm.m
            begin
                cu_if.fu_m = FU_M_GEMM;
                cu_if.m_reg_write = '1;
                cu_if.fu_t = FU_G_T;
            end
      default: dummy = '0;
      endcase
    end

endmodule