`timescale 1ns / 10ps
`include "scoreboard_if.vh"
`include "datapath_types.vh"
`include "isa_types.vh"


import isa_pkg::*;
import datapath_pkg::*;

module scoreboard_tb;

    parameter PERIOD = 10;
    logic CLK = 0, nRST;

    always #(PERIOD/2) CLK++;

    scoreboard_if sbif();

    test PROG (.CLK(CLK), .nRST(nRST), .sbif(sbif));

    scoreboard DUT (.CLK(CLK), .nRST(nRST), .sbif(sbif));

endmodule

program test (
    input logic CLK, 
    output logic nRST,
    scoreboard_if.tb sbif
);

    task reset_dut;
        begin
            nRST = 1'b0;

            @(posedge CLK);
            @(posedge CLK);

            @(negedge CLK);
            nRST = 1'b1;

            @(negedge CLK);
            @(negedge CLK);
        end
    endtask

    task reset_in;
        begin
            // sbif.flush = '0;
            // sbif.freeze = '0;
            // sbif.wb = '0;
            sbif.fetch = '0;
            sbif.wb_issue = '0;
            sbif.wb_dispatch = '0;
            sbif.branch_miss = 1'b0;
            sbif.branch_resolved = 1'b0;
            sbif.fu_ex = '0;
            @(posedge CLK);
        end
    endtask

    task rtype_instr;
        input opcode_t opcode;
        input regbits_t rd;
        input regbits_t rs1;
        input regbits_t rs2;
        input funct3_r_t funct3;
        input funct7_r_t funct7;
        begin
            sbif.fetch.imemload = {funct7, rs2, rs1, funct3, rd, opcode};
            @(posedge CLK);
        end
    endtask

    task itype_instr;
        input opcode_t opcode;
        input regbits_t rd;
        input regbits_t rs1;
        input funct3_i_t funct3;
        input logic [11:0] imm;
        begin
            sbif.fetch.imemload = {imm, rs1, funct3, rd, opcode};
            @(posedge CLK);
        end
    endtask

    task stype_instr;
        input opcode_t opcode;
        input regbits_t rs1;
        input regbits_t rs2;
        input logic [2:0] funct3;
        input logic [11:0] imm;
        begin
            sbif.fetch.imemload = {imm[11:5], rs2, rs1, funct3, imm[4:0], opcode};
            @(posedge CLK);
        end
    endtask

    task btype_instr;
        input opcode_t opcode;
        input regbits_t rs1;
        input regbits_t rs2;
        input funct3_b_t funct3;
        input logic [12:0] imm;
        begin
            sbif.fetch.imemload = {imm[12], imm[10:5], rs2, rs1, funct3, imm[4:1], imm[11], opcode};
            @(posedge CLK);
        end
    endtask

    task jtype_instr;
        input opcode_t opcode;
        input regbits_t rd;
        input logic [20:0] imm;
        begin
            sbif.fetch.imemload = {imm[20], imm[10:1], imm[11], imm[19:12], rd, opcode};
            @(posedge CLK);
        end
    endtask

    task utype_instr;
        input regbits_t rd;
        input logic [20:0] imm;
        begin
            sbif.fetch.imemload = {imm, rd, LUI};
            @(posedge CLK);
        end
    endtask

    task m_ls_instr;
        input opcode_t opcode;
        input matbits_t rd;
        input regbits_t rs1;     // reg file register that holds location of matrix wanted
        input regbits_t stride;  // offset
        input logic [10:0] imm;
        begin
            sbif.fetch.imemload = {rd, rs1, stride, imm[10:0], opcode};
            @(posedge CLK);
        end
    endtask

    task gemm_instr;
        input opcode_t opcode;
        input matbits_t rd;
        input matbits_t ra;
        input matbits_t rb;
        input matbits_t rc;
        begin
            sbif.fetch.imemload = {rd, ra, rb, rc, 9'd0, opcode};
            @(posedge CLK);
        end
    endtask

    initial begin

        reset_in();
        reset_dut();

        @(posedge CLK);
        
        // matrix instructions 

        // rtype_instr(RTYPE, 5'd11, 5'd12, 5'd13, ADD_SUB, ADD);
        // // sbif.fetch = '0;
        // // @(posedge CLK);
        // rtype_instr(RTYPE, 5'd15, 5'd14, 5'd16, ADD_SUB, ADD);
        // sbif.fetch = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.fu_ex[0] = 1'b1;
        // @(posedge CLK);

        // sbif.fu_ex[0] = 1'b0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.fu_ex[0] = 1'b1;
        // @(posedge CLK);

        // sbif.fu_ex[0] = 1'b0;

        // @(posedge CLK);
        // utype_instr(5'd27, 'h44);
        // sbif.fetch = '0;
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // sbif.fu_ex[0] = 1'b1;
        // @(posedge CLK);
        // sbif.fu_ex[0] = 1'b0;
        // repeat (10) @(posedge CLK);
        // rtype_instr(RTYPE, 5'd5, 5'd12, 5'd13, ADD_SUB, ADD);

        // sbif.fetch.br_pc = 32'd200;
        // sbif.fetch.br_pred = 1'b1;
        // btype_instr(BTYPE, 5'd5, 5'd6, BEQ, 13'd0);
        // // rtype_instr(RTYPE, 5'd11, 5'd12, 5'd13, ADD_SUB, ADD);
        // // rtype_instr(RTYPE, 5'd14, 5'd15, 5'd16, ADD_SUB, ADD);
        // // itype_instr(ITYPE_LW, 5'd8, 5'd9, funct3_i_t'(3'h2), 12'd0);

        // sbif.fetch = '0;
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.fu_ex[0] = 1'b1;

        // @(posedge CLK);
        // sbif.fu_ex[0] = 1'b0;

        // // sbif.wb.alu_done = '1;
        // // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_issue.wdat = 32'd124;

        // sbif.wb_dispatch.s_rw_en = '1;
        // sbif.wb_dispatch.s_rw = 5'd5;

        // sbif.wb_issue.reg_en = '1;
        // sbif.wb_issue.reg_sel = 5'd5;

        // @(posedge CLK);

        // itype_instr(ITYPE_LW, 5'd12, 5'd15, funct3_i_t'(3'h2), 12'd16);
        // sbif.fetch = '0;

        // sbif.wb_issue.wdat = '0;

        // sbif.wb_dispatch.s_rw_en = '0;
        // sbif.wb_dispatch.s_rw = '0;

        // sbif.wb_issue.reg_en = '0;
        // sbif.wb_issue.reg_sel = '0;
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);


        // sbif.fu_ex[2] = 1'b1;
        // sbif.fu_ex[1] = 1'b1;
        // // sbif.branch_miss = 1'b1;

        // @(posedge CLK);

        // sbif.fu_ex = '0;
        // sbif.branch_miss = 0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.fetch.br_pc = 32'd240;
        // sbif.fetch.br_pred = 1'b0;
        // btype_instr(BTYPE, 5'd15, 5'd5, BNE, 13'd0);
        // sbif.fetch = '0;

        // repeat (10) @(posedge CLK);

        // sbif.fu_ex[2] = 1'b1;
        // sbif.branch_resolved = 1'b1;

        // @(posedge CLK);

        // sbif.fu_ex[2] = 1'b0;
        // sbif.branch_resolved = 1'b0;

        // rtype_instr(RTYPE, 5'd15, 5'd22, 5'd23, ADD_SUB, ADD);
        // sbif.fetch = '0;

        // @(posedge CLK);

        // sbif.fetch.br_pc = 32'd241;
        // itype_instr(JALR, 5'd20, 5'd5, funct3_i_t'(3'h0), 12'd16); // JALR
        // // jtype_instr(JAL, 5'd20, 12'd16); // JAL
        // sbif.fetch = '0;
        // sbif.fetch.br_pc = '0;

        // repeat (3) @(posedge CLK);

        // sbif.fu_ex[0] = 1'b1;
        // @(posedge CLK);
        // sbif.fu_ex[0] = 1'b0;

        // repeat (4) @(posedge CLK);

        // sbif.fu_ex[2] = 1'b1;
        // sbif.branch_resolved = 1'b1;
        // @(posedge CLK);
        // sbif.fu_ex[2] = 1'b0;
        // sbif.branch_resolved = 1'b0;

        // repeat (10) @(posedge CLK);

        sbif.fetch = '1;
        
        repeat (10) @(posedge CLK);



        // @(posedge CLK);
        // rtype_instr(RTYPE, 5'd10, 5'd11, 5'd12, ADD_SUB, ADD);
        // itype_instr(ITYPE_LW, 5'd8, 5'd9, funct3_i_t'(3'h2), 12'd210);
        // itype_instr(ITYPE, 5'd18, 5'd19, ADDI, 12'd110);
        // sbif.fetch = '0;

        // repeat (3) begin
        //     @(posedge CLK);
        // end

        // stype_instr;
        // input opcode_t opcode;
        // input regbits_t rs1;
        // input regbits_t rs2;
        // input logic [2:0] funct3;
        // input logic [11:0] imm;



        // // fu_ex as writeback now

        // rtype_instr(RTYPE, 5'd10, 5'd11, 5'd12, ADD_SUB, ADD);
        // rtype_instr(RTYPE, 5'd15, 5'd16, 5'd14, ADD_SUB, ADD);
        // sbif.fetch.imemload = '0;

        // @(posedge CLK);

        // sbif.fu_ex = ALU_DONE;

        // repeat (10) begin
        //     @(posedge CLK);
        // end

        // branch resolution 
        // sbif.fetch.br_pc = 32'd200;
        // sbif.fetch.br_pred = 1'b1;
        // btype_instr(BTYPE, 5'd5, 5'd6, BEQ, 13'd0);
        // rtype_instr(RTYPE, 5'd11, 5'd12, 5'd13, ADD_SUB, ADD);
        // rtype_instr(RTYPE, 5'd14, 5'd15, 5'd16, ADD_SUB, ADD);
        // itype_instr(ITYPE_LW, 5'd8, 5'd9, funct3_i_t'(3'h2), 12'd0);
        
        // @(posedge CLK);
        // rtype_instr(RTYPE, 5'd5, 5'd12, 5'd13, ADD_SUB, ADD);
        // rtype_instr(RTYPE, 5'd15, 5'd22, 5'd23, ADD_SUB, ADD);
        // sbif.fu_ex[0] = 1'b1;
        // @(posedge CLK);
        // sbif.fu_ex[0] = 1'b0;
        // sbif.fetch = '0;
        // sbif.wb_issue.s_wdata = 32'd124;

        // sbif.wb_dispatch.s_rw_en = '1;
        // sbif.wb_dispatch.s_rw = 5'd5;

        // sbif.wb_issue.s_rw_en = '1;
        // sbif.wb_issue.s_rw = 5'd5;
        // @(posedge CLK);
        
        // sbif.wb_issue.s_wdata = '0;

        // sbif.wb_dispatch.s_rw_en = '0;
        // sbif.wb_dispatch.s_rw = '0;

        // sbif.wb_issue.s_rw_en = '0;
        // sbif.wb_issue.s_rw = '0;
        // sbif.fu_ex[0] = 1'b1;

        // @(posedge CLK);
        // sbif.fu_ex[0] = 1'b0;
        // @(posedge CLK);
        
        // @(posedge CLK);


        // @(posedge CLK);

        // // sbif.wb.alu_done = '1;
        // // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb.s_wdata = 32'd124;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd5;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd5;

        // @(posedge CLK);

        // itype_instr(ITYPE_LW, 5'd12, 5'd15, funct3_i_t'(3'h2), 12'd16);
        // sbif.fetch = '0;

        // sbif.wb.s_wdata = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);


        // sbif.fu_ex = BRANCH_DONE;
        // sbif.branch_miss = 1;

        // @(posedge CLK);

        // sbif.fu_ex = fu_done_signals'('0);
        // sbif.branch_miss = 0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.fetch.br_pc = 32'd240;
        // sbif.fetch.br_pred = 1'b0;
        // btype_instr(BTYPE, 5'd15, 5'd5, BEQ, 13'd0);
        // sbif.fetch = '0;

        // repeat (10) @(posedge CLK);

        // sbif.fetch = '1;

        // repeat (10) @(posedge CLK);

        // //  age check
        // itype_instr(ITYPE_LW, 5'd5, 5'd6, funct3_i_t'(3'h2), 12'd0);
        // rtype_instr(RTYPE, 5'd11, 5'd5, 5'd10, ADD_SUB, ADD);
        // btype_instr(BTYPE, 5'd5, 5'd15, BEQ, 13'd0);

        // sbif.fetch.imemload = '0;

        // repeat (10) begin
        //     @(posedge CLK);
        // end


        // sbif.wb.load_done = '1;
        // sbif.wb_ctrl.load_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd5;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd5;

        // sbif.s_wdata = 32'd101;

        // @(posedge CLK);

        // sbif.wb.load_done = '0;
        // sbif.wb_ctrl.load_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd11;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd11;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;


        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);


        // (opcode, rd, rs1, rs2, funct3, funct7)
        // rtype_instr(RTYPE, 5'd10, 5'd11, 5'd12, ADD_SUB, ADD);
        // rtype_instr(RTYPE, 5'd15, 5'd16, 5'd14, ADD_SUB, ADD);
        // sbif.fetch.imemload = '0;

        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd10;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd10;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd10;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd10;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // reset_in();
        // reset_dut();

        // @(posedge CLK);

        // itype_instr(ITYPE_LW, 5'd4, 5'd6, funct3_i_t'(3'h2), 12'd0);
        // rtype_instr(RTYPE, 5'd10, 5'd4, 5'd12, ADD_SUB, ADD); 
        // sbif.fetch.imemload = '0;

        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.load_done = '1;
        // sbif.wb_ctrl.load_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd4;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd4;

        // @(posedge CLK);

        // sbif.wb.load_done = '0;
        // sbif.wb_ctrl.load_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd10;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd10;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // // out of order 

        // itype_instr(ITYPE_LW, 5'd5, 5'd7, funct3_i_t'(3'h2), 12'd0);
        // rtype_instr(RTYPE, 5'd10, 5'd9, 5'd12, ADD_SUB, ADD); // 1
        // sbif.fetch.imemload = '0;

        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd10;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd10;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);

        // rtype_instr(RTYPE, 5'd11, 5'd13, 5'd14, ADD_SUB, ADD); // 2
        // sbif.fetch.imemload = '0;

        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd11;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd11;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);

        // rtype_instr(RTYPE, 5'd17, 5'd15, 5'd16, ADD_SUB, ADD); // 3
        // sbif.fetch.imemload = '0;

        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.alu_done = '1;
        // sbif.wb_ctrl.alu_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd17;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd17;

        // @(posedge CLK);

        // sbif.wb.alu_done = '0;
        // sbif.wb_ctrl.alu_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);

        // sbif.wb.load_done = '1;
        // sbif.wb_ctrl.load_done = '1;

        // sbif.wb_ctrl.s_rw_en = '1;
        // sbif.wb_ctrl.s_rw = 5'd5;

        // sbif.wb.s_rw_en = '1;
        // sbif.wb.s_rw = 5'd5;

        // @(posedge CLK);

        // sbif.wb.load_done = '0;
        // sbif.wb_ctrl.load_done = '0;

        // sbif.wb_ctrl.s_rw_en = '0;
        // sbif.wb_ctrl.s_rw = '0;

        // sbif.wb.s_rw_en = '0;
        // sbif.wb.s_rw = '0;

        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);
        // @(posedge CLK);


        // // once that instruction is done and wb sends done, send second instruction
        // // allow second instruction to go through 
        // // do the same as above but add a load/store instruction for the third instruction 
        // // let it all go through 

        // // do three s type instructions all back to back no dependencies
        
        // // do three s type instructions all back to back with dependencies 
        // // do three i type (lw) instructions all back to back no dependencies
        
        // // do three i type (lw) instructions all back to back with dependencies 
        // // mix and match the above
        // // go into matrix stuff now, similar to the above stuff

        // @(posedge CLK);
        // @(posedge CLK);
        

        $finish;
    end


endprogram
