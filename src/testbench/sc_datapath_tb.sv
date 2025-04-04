`include "pipeline_types.vh"
`include "datapath_types.vh"
`include "isa_types.vh"

// INTERFACES
`include "fetch_if.vh"
`include "scoreboard_if.vh"
`include "dispatch_if.vh"
`include "issue_if.vh"
`include "regfile_if.vh"
`include "execute_if.vh"
`include "writeback_if.vh"
`include "datapath_cache_if.vh"

`timescale 1 ns / 10ps

import isa_pkg::*;
import datapath_pkg::*;

module sc_datapath_tb;
  // clock period
  parameter PERIOD = 10;

  // signals
  logic CLK = 1, nrst;

  // clock
  always #(PERIOD/2) CLK++;

  // interface
  datapath_cache_if                   dcif ();

  // dut
  sc_datapath                         DUT (.CLK(CLK), .nrst(nrst), .dcif(dcif));

  test                                PROG (.CLK(CLK), .nrst(nrst), .dcif(dcif));

endmodule

program test(input logic CLK, output logic nrst, datapath_cache_if.tb dcif);

  task rtype_instr;
        input regbits_t rd;
        input regbits_t rs1;
        input regbits_t rs2;
        input funct3_r_t funct3;
        input funct7_r_t funct7;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {funct7, rs2, rs1, funct3, rd, RTYPE};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task itype_instr;
        input regbits_t rd;
        input regbits_t rs1;
        input logic [11:0] imm;
        input funct3_i_t funct3;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {imm, rs1, funct3, rd, ITYPE};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task itype_lw_instr;
        input regbits_t rd;
        input regbits_t rs1;
        input logic [11:0] imm;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {imm, rs1, funct3_i_t'(3'h2), rd, ITYPE_LW};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task stype_instr;
        input regbits_t rs1;
        input regbits_t rs2;
        input logic [2:0] funct3;
        input logic [11:0] imm;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {imm[11:5], rs2, rs1, funct3, imm[4:0], STYPE};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task btype_instr;
        input regbits_t rs1;
        input regbits_t rs2;
        input funct3_b_t funct3;
        input logic [12:0] imm;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {imm[12], imm[10:5], rs2, rs1, funct3, imm[4:1], imm[11], BTYPE};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task jtype_instr;
        input regbits_t rd;
        input logic [20:0] imm;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {imm[20], imm[10:1], imm[11], imm[19:12], rd, JAL};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task itype_jalr_instr;
        input regbits_t rd;
        input regbits_t rs1;
        input logic [11:0] imm;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = {imm, rs1, funct3_i_t'(3'h0), rd, JALR};
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    task m_ls_instr;
        input opcode_t opcode;
        input matbits_t rd;
        input regbits_t rs1;     // reg file register that holds location of matrix wanted
        input regbits_t stride;  // offset
        input logic [10:0] imm;
        begin
            dcif.imemload = {rd, rs1, stride, imm[10:0], opcode};
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
            dcif.imemload = {rd, ra, rb, rc, 9'd0, opcode};
            @(posedge CLK);
        end
    endtask

    task halt;
        begin
            if (dcif.imemREN == 1'b1) begin
                @(posedge CLK);
                dcif.imemload = '1; // halt
                dcif.ihit = 1'b1;
                @(posedge CLK);
                dcif.imemload = '0;
                dcif.ihit = 1'b0;
                @(posedge CLK);
            end
        end
    endtask

    string tb_test_case = "INIT";

    initial begin 
        nrst = 0;
        dcif.imemload = '0;
        dcif.ihit = 0;
        dcif.dhit = '0;
        dcif.mhit = '0;
        dcif.dmemload = '0;

        @(posedge CLK);
        nrst = 1'b1;

        @(posedge CLK);
        tb_test_case = "LW";
        itype_lw_instr(5'd12, 5'd15, 12'd16);
        tb_test_case = "ADDI";
        itype_instr(5'd11, 5'd13, 'd125, ADDI);

        repeat (7) @(posedge CLK);
        dcif.dhit = 1'b1;
        dcif.dmemload = 'd135;
        @(posedge CLK);

        dcif.dhit = 1'b0;
        dcif.dmemload = '0;
        @(posedge CLK);
        
        // tb_test_case = "JTYPE";
        // jtype_instr(5'd20, 'd110);
        // repeat (3) @(posedge CLK);

        tb_test_case = "BEQ";
        btype_instr(11, 12, BEQ, 13'hBAC);
        repeat (3) @(posedge CLK);

        tb_test_case = "ADDI";
        itype_instr(5, 7, 12'h0A0, ADDI);
        repeat (10) @(posedge CLK);

        tb_test_case = "ADDI 2";
        itype_instr(6, 7, 12'h0B0, ADDI);
        repeat (10) @(posedge CLK);

        tb_test_case = "BNE";
        btype_instr(5, 6, BNE, 13'hBA0);
        repeat (10) @(posedge CLK);

        tb_test_case = "HALT";
        halt();
        
        repeat (15) @(posedge CLK);

        $finish;
    end

endprogram

