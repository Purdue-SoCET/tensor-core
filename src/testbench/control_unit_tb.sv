// control unit testbench
// lab 4
// rrbathin
// 9/5/2024

// mapped needs this
`include "control_unit_if.vh"

// mapped timing needs this. 1ns is too fast
`timescale 1 ns / 1 ns

module control_unit_tb;

    control_unit_if ctrlif ();

    test PROG (ctrlif);

    control_unit DUT(.cu_if(ctrlif));

endmodule

// program test(
//     control_unit_if.tb ctrl_if
// );

//     parameter PERIOD = 10ns;

//     // mem
//     parameter WRITE = 2;
//     parameter READ = 1;
//     parameter TO_REG = 0;

//     // branch
//     parameter BEQ = 0;
//     parameter BNE = 1;
//     parameter BLT = 2;
//     parameter BGE = 3;
//     parameter BLTU = 4;
//     parameter BGEU = 5;

//     // u type
//     parameter LOAD = 0;
//     parameter ADD = 1;

//     integer test_num;

//     task run_test;
//         input logic [6:0] tb_opcode;
//         input logic [6:0] tb_funct7;
//         input logic [2:0] tb_funct3;
//     begin 
//         // ctrl_if.opcode = tb_opcode; // not in the interface
//         // ctrl_if.funct7 = tb_funct7;
//         // ctrl_if.funct3 = tb_funct3;
//         #(PERIOD);
//     end
//     endtask

//     task check_outputs;
//         input logic tb_halt_pre; 
//         // input logic [5:0] tb_b_type; 
//         input logic tb_i_flag; 
//         input logic [2:0] tb_mem_type; 
//         input logic tb_reg_write; 
//         input logic tb_jalr; 
//         input logic tb_jal; 
//         input logic [1:0] tb_u_type; 
//         input logic [3:0] tb_alu_op; 
//         input logic [2:0] tb_branch_type;
//         input integer tb_test_num;
//     begin 
//         // if (ctrl_if.halt_pre != tb_halt_pre)
//         //     $display("Incorrect halt test# %d", tb_test_num);
//         // if (ctrl_if.b_type != tb_b_type)
//         //     $display("Incorrect branch test# %d", tb_test_num);
//         if (ctrl_if.i_flag != tb_i_flag)
//             $display("Incorrect i type flag test# %d", tb_test_num);
//         // if (ctrl_if.mem_type != tb_mem_type)
//         //     $display("Incorrect mem type test# %d", tb_test_num);
//         if (ctrl_if.reg_write != tb_reg_write)
//             $display("Incorrect reg write test# %d", tb_test_num);
//         if (ctrl_if.jalr != tb_jalr)
//             $display("Incorrect jalr test# %d", tb_test_num);
//         if (ctrl_if.jal != tb_jal)
//             $display("Incorrect jal test# %d", tb_test_num);
//         if (ctrl_if.u_type != tb_u_type)
//             $display("Incorrect u type test# %d", tb_test_num);
//         if (ctrl_if.alu_op != tb_alu_op)
//             $display("Incorrect alu op test# %d", tb_test_num);
//         if (ctrl_if.branch_type != tb_branch_type)
//             $display("Incorrect branch type test# %d", tb_test_num);
//     end
//     endtask

//     task reset;
//     begin 
//         // ctrl_if.opcode = '0; // not in interface
//         // ctrl_if.funct7 = '0;
//         // ctrl_if.funct3 = '0;
//     end
//     endtask
        

//     initial begin
//         reset();
//         test_num = 0;
//         #(PERIOD);

//         test_num += 1; // 1
//         run_test('0,'0,'0);
//         check_outputs('0, '0, '0, '0, '0, '0, '0, '0, '0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // r-type

//         test_num += 1; // 2
//         run_test(7'b0110011, 7'b0, 3'b0);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b0, 4'b0011, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 3
//         run_test(7'b0110011, 7'h20, 3'b0);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b0, 4'b0100, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 4
//         run_test(7'b0110011, 7'h00, 3'h7);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b0, 4'b0101, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 5
//         run_test(7'b0110011, 7'h00, 3'h5);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b0, 4'b0001, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 6
//         run_test(7'b0110011, 7'h20, 3'h5);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b0, 4'b0010, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // i-type

//         test_num += 1; // 7
//         run_test(7'b0010011, 7'h00, 3'h0);
//         check_outputs('0, '1, 3'b0, '1, '0, '0, 2'b0, 4'b0011, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 8
//         run_test(7'b0010011, 7'h00, 3'h2);
//         check_outputs('0, '1, 3'b0, '1, '0, '0, 2'b0, 4'b1010, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 9
//         run_test(7'b0010011, 7'h00, 3'h5);
//         check_outputs('0, '1, 3'b0, '1, '0, '0, 2'b0, 4'b0001, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 10
//         run_test(7'b0010011, 7'h20, 3'h5);
//         check_outputs('0, '1, 3'b0, '1, '0, '0, 2'b0, 4'b0010, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // i-type lw

//         test_num += 1; // 11
//         run_test(7'b0000011, 7'h00, 3'h2);
//         check_outputs('0, '1, 3'b011, '1, '0, '0, 2'b0, 4'b0011, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // jalr

//         test_num += 1; // 12
//         run_test(7'b1100111, 7'h00, 3'h0);
//         check_outputs('0, '1, 3'b000, '1, '1, '0, 2'b0, 4'b0011, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // s-type

//         test_num += 1; // 13
//         run_test(7'b0100011, 7'h00, 3'h2);
//         check_outputs('0, '1, 3'b100, '0, '0, '0, 2'b0, 4'b0011, 3'b0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // b-type

//         test_num += 1; // 14
//         run_test(7'b1100011, 7'h00, 3'h0);
//         check_outputs('0, '0, 3'b0, '0, '0, '0, 2'b0, 4'b0100, 3'd1, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 15
//         run_test(7'b1100011, 7'h00, 3'h5);
//         check_outputs('0, '0, 3'b0, '0, '0, '0, 2'b0, 4'b0100, 3'd4, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         test_num += 1; // 16
//         run_test(7'b1100011, 7'h00, 3'h6);
//         check_outputs('0, '0, 3'b0, '0, '0, '0, 2'b0, 4'b1011, 3'd5, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // j-type

//         test_num += 1; // 17
//         run_test(7'b1101111, 7'h00, 3'h0);
//         check_outputs('0, '1, 3'b0, '1, '0, '1, 2'b0, 4'b0011, 3'd0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // lui

//         test_num += 1; // 18
//         run_test(7'b0110111, 7'h00, 3'h0);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b01, 4'b0, 3'd0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // auipc

//         test_num += 1; // 19
//         run_test(7'b0010111, 7'h00, 3'h0);
//         check_outputs('0, '0, 3'b0, '1, '0, '0, 2'b10, 4'b0, 3'd0, test_num);

//         #(PERIOD);
//         #(PERIOD);

//         // halt

//         test_num += 1; // 20
//         run_test(7'b1111111, 7'h00, 3'h0);
//         check_outputs('1, '0, 3'b0, '0, '0, '0, 2'b0, 4'b0, 3'd0, test_num);

//         #(PERIOD);
//         #(PERIOD);


//     end


// endprogram