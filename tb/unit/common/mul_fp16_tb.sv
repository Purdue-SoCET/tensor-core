`timescale 1ns/1ps


// ./obj_dir/VMAC_unit_tb
// gtkwave waves.vcd --save=mac_debug.gtkw

// to run this: verilator --binary -j 0 -Wall -Wno-fatal mul_fp16_tb -Imodules -Itestbench -Iinclude --hierarchical --trace; ./obj_dir/Vmul_fp16_tb; gtkwave mul_fp16_waves.vcd --save=mul_fp16_debug.gtkw


/* verilator lint_off UNUSEDSIGNAL */
module mul_fp16_tb;

    // Parameters
    localparam CLK_PERIOD = 1;

    // Testbench Signals
    logic tb_clk;
    logic tb_nrst;
    integer i;

    // Clk init
    always
    begin
        tb_clk = 1'b0;
        #(CLK_PERIOD/2.0);
        tb_clk = 1'b1;
        #(CLK_PERIOD/2.0);
    end
    
    logic [15:0] tb_a, tb_b;
    logic tb_start;
    logic [15:0] tb_result;
    logic tb_done;

    mul_fp16 melvin (.clk(tb_clk), .nRST(tb_nrst), .start(tb_start), .a(tb_a), .b(tb_b), .result(tb_result), .done(tb_done));

    logic [15:0] test_set1[9:0];
    logic [15:0] test_set2[9:0];
    logic [15:0] test_set3[9:0];

    
    // Test sequence
    initial begin
        // Initialize interface signals
        $dumpfile("mul_fp16_waves.vcd");
        $dumpvars();
        tb_nrst = 0;
        #CLK_PERIOD;
        tb_nrst = 1;

        test_set1[0] = 16'h4720;
        test_set1[1] = 16'h4491;
        test_set1[2] = 16'h487e;
        test_set1[3] = 16'h456f;
        test_set1[4] = 16'h4854;
        test_set1[5] = 16'h458b;
        test_set1[6] = 16'h403f;
        test_set1[7] = 16'h489e;
        test_set1[8] = 16'h47e0;
        test_set1[9] = 16'h48f0;

        test_set2[0] = 16'h41c1;
        test_set2[1] = 16'h4620;
        test_set2[2] = 16'h4849;
        test_set2[3] = 16'h46fd;
        test_set2[4] = 16'h463c;
        test_set2[5] = 16'h4420;
        test_set2[6] = 16'h3ff3;
        test_set2[7] = 16'h435c;
        test_set2[8] = 16'h40b1;
        test_set2[9] = 16'h43fa;

        test_set3[0] = 16'h48c9;
        test_set3[1] = 16'h3cf0;
        test_set3[2] = 16'h40dd;
        test_set3[3] = 16'h48ac;
        test_set3[4] = 16'h47fd;
        test_set3[5] = 16'h3e2c;
        test_set3[6] = 16'h476f;
        test_set3[7] = 16'h47a8;
        test_set3[8] = 16'h3dba;
        test_set3[9] = 16'h4388;

        @(posedge tb_clk);
        tb_start = 0;

        // Test pattern 2: Continuous stream of instructions
        for(i = 0; i < 10; i++) begin
            tb_start = 1'b0;
            tb_a = test_set1[i];
            tb_b = test_set2[i];
            tb_start = 1'b1;
            #CLK_PERIOD;
            tb_start = 1'b0;
          
        //    $display("Input: %h   Weight: %h   in_acc: %h    MAC Unit Output: %h", test_inputs[i], test_weights[i], test_ps[i], mac_if.out_accumulate);
        //    #CLK_PERIOD;
        //    #CLK_PERIOD;
        end
        @(negedge tb_done);
        $finish;
    end

endmodule

