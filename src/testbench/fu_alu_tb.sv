`include "fu_alu_if.vh"
`include "isa_types.vh"

`timescale 1 ns / 1 ns

import isa_pkg::*;

module fu_alu_tb;
  string tb_test_case = "INIT";
  logic CLK = 0;
  parameter PERIOD = 10;

  always #(PERIOD/2) CLK++;

  fu_alu_if aluif ();
  fu_alu DUT(.aluif(aluif));

  initial begin
    tb_test_case = "SLL: Case 1";
    aluif.port_a = 32'd8;
    aluif.port_b = 32'd1;
    aluif.aluop = 4'd0;
    #(100);

    tb_test_case = "SRL: Case 1";
    aluif.port_a = 32'd8;
    aluif.port_b = 32'd1;
    aluif.aluop = 4'd1;
    #(100);

    tb_test_case = "SRA: Case 1";
    aluif.port_a = 32'b11000000000000000000000000000000;
    aluif.port_b = 32'd1;
    aluif.aluop = 4'd2;
    #(100);

    tb_test_case = "ADD: Case 1";
    aluif.port_a = 32'd2;
    aluif.port_b = 32'd3;
    aluif.aluop = 4'd3;
    #(100);

    tb_test_case = "SUB: Case 1";
    aluif.port_a = 32'd6;
    aluif.port_b = 32'd2;
    aluif.aluop = 4'd4;
    #(100);

    tb_test_case = "AND: Case 1";
    aluif.port_a = 32'h0000FFFF;
    aluif.port_b = 32'h0000F0E0;
    aluif.aluop = 4'd5;
    #(100);

    tb_test_case = "OR: Case 1";
    aluif.port_a = 32'h0000FFFF;
    aluif.port_b = 32'h0000F0E0;
    aluif.aluop = 4'd6;
    #(100);

    tb_test_case = "XOR: Case 1";
    aluif.port_a = 32'h0000FFFF;
    aluif.port_b = 32'h0000F0E0;
    aluif.aluop = 4'd7;
    #(100);

    tb_test_case = "SLT: Case 1";
    aluif.port_a = 32'h0000F0E0;
    aluif.port_b = 32'h0000FFE0;
    aluif.aluop = 4'd10;
    #(100);

    tb_test_case = "SLTU: Case 1";
    aluif.port_a = 32'hF000FFE0;
    aluif.port_b = 32'h0000F0E0;
    aluif.aluop = 4'd11;
    #(100);

    $stop;
  end
endmodule