// control unit

// need to include matrix related instructions, gemm, ld.m, sw.m

`include "types_pkg.vh"
`include "control_unit_if.vh"

module control_unit(
    control_unit_if.cu cu_if
);

    import types_pkg::*;

    word_t instr;

    assign instr = cu_if.instr;

    always_comb begin
      cu_if.halt = '0;
      cu_if.i_flag = '0;
      cu_if.s_mem_type = '0;
      cu_if.reg_write = '0;
      cu_if.jalr = '0;
      cu_if.jal = '0;
      cu_if.u_type = '0;
      cu_if.alu_op = '0;
      cu_if.branch_type = '0;
      cu_if.imm = '0;
      cu_if.stride = '0;
      cu_if.fu_s = '0;
      cu_if.fu_m = '0;
      cu_if.m_mem_type = '0;
      cu_if.matrix_rd = '0;
      cu_if.matrix_rs1 = '0;
      casez (instr[6:0])
        RTYPE:
            begin 
                cu_if.reg_write = '1;
                cu_if.fu_s = ALU;
                casez(instr[14:12])
                    SLL: cu_if.alu_op = ALU_SLL;
                    SRL_SRA: cu_if.alu_op = (instr[31:25] == SRA) ? ALU_SRA : ALU_SRL;
                    ADD_SUB: cu_if.alu_op = (instr[31:25] == SUB) ? ALU_SUB : ALU_ADD;
                    AND: cu_if.alu_op = ALU_AND;
                    OR: cu_if.alu_op = ALU_OR;
                    XOR: cu_if.alu_op = ALU_XOR;
                    SLT: cu_if.alu_op = ALU_SLT;
                    SLTU: cu_if.alu_op = ALU_SLTU;
                endcase
            end
        ITYPE: 
            begin 
                cu_if.reg_write = '1;
                cu_if.i_flag = '1;
                cu_if.imm = $signed({instr[31:20]});
                cu_if.fu_s = ALU;
                casez(instr[14:12])
                    ADDI: cu_if.alu_op = ALU_ADD;
                    XORI: cu_if.alu_op = ALU_XOR;
                    ORI: cu_if.alu_op = ALU_OR;
                    ANDI: cu_if.alu_op = ALU_AND;
                    SLLI: cu_if.alu_op = ALU_SLL;
                    SRLI_SRAI: cu_if.alu_op = (instr[31:25] == 7'h20) ? ALU_SRA : ALU_SRL;
                    SLTI: cu_if.alu_op = ALU_SLT;
                    SLTIU: cu_if.alu_op = ALU_SLTU;
                endcase
            end
        ITYPE_LW:
            begin
                if (instr[14:12] == 3'h2) begin 
                    cu_if.imm = $signed({instr[31:20]});
                    cu_if.reg_write = '1;
                    cu_if.i_flag = '1;
                    // cu_if.alu_op = ALU_ADD;
                    cu_if.s_mem_type = MEM_TO_REG;
                    cu_if.s_mem_type = LOAD;
                    cu_if.fu_s = LD_ST;
                end
            end
        JALR:
            begin 
                cu_if.imm = $signed({instr[31:20]});
                cu_if.reg_write = '1;
                cu_if.jalr = '1;
                cu_if.alu_op = ALU_ADD;
                cu_if.i_flag = '1;
                cu_if.fu_s = ALU;
            end
        STYPE:
            begin
                if (instr[14:12] == 3'h2) begin 
                    cu_if.imm = $signed({instr[31:25], instr[11:7]});
                    cu_if.i_flag = '1;
                    // cu_if.alu_op = ALU_ADD
                    cu_if.s_mem_type = STORE;
                    cu_if.fu_s = LD_ST;
                end 
            end
        BTYPE:
            begin 
                // cu_if.reg_write = '1;
                cu_if.imm = $signed({instr[31], instr[7], instr[30:25], instr[11:8], 1'b0});
                cu_if.fu_s = BRANCH;
                casez(instr[14:12])
                    BEQ: 
                        begin 
                            cu_if.branch_type = BEQ; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_type = 3'd1;
                        end
                    BNE: 
                        begin 
                            cu_if.branch_type = BNE; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_type = 3'd2;
                        end
                    BLT: 
                        begin 
                            cu_if.branch_type = BLT; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_type = 3'd3;
                        end
                    BGE: 
                        begin 
                            cu_if.branch_type = BGE; 
                            // cu_if.alu_op = ALU_SUB;
                            // cu_if.branch_type = 3'd4;
                        end
                    BLTU: 
                        begin 
                            cu_if.branch_type = BLTU; 
                            // cu_if.alu_op = ALU_SLTU;
                            // cu_if.branch_type = 3'd5;
                        end
                    BGEU: 
                        begin 
                            cu_if.branch_type = BGEU; 
                            // cu_if.alu_op = ALU_SLTU;
                            // cu_if.branch_type = 3'd6;
                        end
                endcase
            end
        JAL:
            begin 
                cu_if.imm = $signed({instr[31], instr[19:12], instr[20], instr[30:21], 1'b0});
                cu_if.jal = '1;
                cu_if.reg_write = '1;
                cu_if.alu_op = ALU_ADD;
                cu_if.i_flag = '1;
                cu_if.fu_s = ALU;
            end
        LUI:
            begin
                cu_if.imm = {instr[31:12], 12'b0};
                cu_if.u_type = LOAD;
                cu_if.reg_write = '1;
            end
        // AUIPC:
        //     begin 
        //         cu_if.u_type = ADD;
        //         cu_if.reg_write = '1;
        //         cu_if.imm = {instr[31:12], 12'b0};
        //     end
        HALT: cu_if.halt = '1;
        7'b1000111: // ld.m
            begin 
                cu_if.imm = $signed({instr[17:7]});
                // cu_if.i_flag = '1;
                // cu_if.alu_op = ALU_ADD;
                cu_if.stride = instr[22:18]; // register
                cu_if.fu = LD_ST;
                cu_if.m_mem_type = LOAD;
                cu_if.matrix_rd = instr[31:28];
                cu_if.matrix_rs1 = instr[27:23];
            end
        7'b1010111: //st.m
            begin
                cu_if.imm = $signed({instr[17:7]});
                // cu_if.i_flag = '1;
                // cu_if.alu_op = ALU_ADD;
                cu_if.stride = instr[22:18]; // register
                cu_if.fu_m = LD_ST;
                cu_if.m_mem_type = STORE;
                cu_if.matrix_rd = instr[31:28];
                cu_if.matrix_rs1 = instr[27:23];
            end
        7'b1110111: // gemm.m "md = ma @ mb + mc"
            begin
                cu_if.fu_m = GEMM;
                //i think thats it?
            end
      endcase
    end

endmodule
