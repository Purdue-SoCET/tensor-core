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
            sbif.flush = '0;
            sbif.freeze = '0;
            sbif.wb = '0;
            sbif.fetch = '0;
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
            // @(posedge CLK);
        end
    endtask

    // add more tasks like the above for each type of instructions including matrix instructions

    initial begin

        reset_in();
        reset_dut();

        @(posedge CLK);

        rtype_instr(RTYPE, 5'd10, 5'd11, 5'd12, ADD_SUB, ADD); // (opcode, rd, rs1, rs2, funct3, funct7)
        rtype_instr(RTYPE, 5'd15, 5'd10, 5'd12, ADD_SUB, ADD);


        @(posedge CLK);
        @(posedge CLK);
        @(posedge CLK);

        $finish;
    end


endprogram
