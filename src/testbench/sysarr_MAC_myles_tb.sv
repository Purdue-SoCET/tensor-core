`timescale 1ns/1ps

`include "systolic_array_MAC_if.vh"

// ./obj_dir/VMAC_unit_tb
// gtkwave waves.vcd --save=mac_debug.gtkw

// to run this: verilator --binary -j 0 -Wall -Wno-fatal sysarr_MAC_tb -Imodules -Itestbench -Iinclude --hierarchical --trace; ./obj_dir/Vsysarr_MAC_tb; gtkwave waves.vcd --save=mac_debug.gtkw


/* verilator lint_off UNUSEDSIGNAL */
module sysarr_MAC_tb;

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
    
    // sysarr_control_unit_if instance
    systolic_array_MAC_if mac_if();

    sysarr_MAC_myles dut (.clk(tb_clk), .nRST(tb_nrst), .mac_if(mac_if.MAC));

    logic [15:0] test_inputs[9:0];
    logic [15:0] test_weights[9:0];
    logic [15:0] test_ps[9:0];

    
    // Test sequence
    initial begin
        // Initialize interface signals
        $dumpfile("waves.vcd");
        $dumpvars();
        tb_nrst = 0;
        #CLK_PERIOD;
        tb_nrst = 1;

        test_inputs[0] = 16'h4720;
        test_inputs[1] = 16'h4491;
        test_inputs[2] = 16'h487e;
        test_inputs[3] = 16'h456f;
        test_inputs[4] = 16'h4854;
        test_inputs[5] = 16'h458b;
        test_inputs[6] = 16'h403f;
        test_inputs[7] = 16'h489e;
        test_inputs[8] = 16'h47e0;
        test_inputs[9] = 16'h48f0;

        test_weights[0] = 16'h41c1;
        test_weights[1] = 16'h4620;
        test_weights[2] = 16'h4849;
        test_weights[3] = 16'h46fd;
        test_weights[4] = 16'h463c;
        test_weights[5] = 16'h4420;
        test_weights[6] = 16'h3ff3;
        test_weights[7] = 16'h435c;
        test_weights[8] = 16'h40b1;
        test_weights[9] = 16'h43fa;

        test_ps[0] = 16'h48c9;
        test_ps[1] = 16'h3cf0;
        test_ps[2] = 16'h40dd;
        test_ps[3] = 16'h48ac;
        test_ps[4] = 16'h47fd;
        test_ps[5] = 16'h3e2c;
        test_ps[6] = 16'h476f;
        test_ps[7] = 16'h47a8;
        test_ps[8] = 16'h3dba;
        test_ps[9] = 16'h4388;

        @(posedge tb_clk);
        mac_if.start = 0;



        for(i = 0; i < 10; i++) begin
           mac_if.weight_en = 1'b0;
           #CLK_PERIOD;
           mac_if.in_value = test_weights[i];
           mac_if.weight_en = 1'b1;
           #CLK_PERIOD;
           mac_if.weight_en = 1'b0;
           mac_if.in_accumulate = test_ps[i];
           mac_if.in_value = test_inputs[i];
           mac_if.MAC_shift = 1'b1;
           #CLK_PERIOD;
           mac_if.MAC_shift = 1'b0;
           mac_if.start = 1'b1;
           #CLK_PERIOD;
           mac_if.start = 1'b0;
           @(posedge mac_if.value_ready);
           $display("Input: %h   Weight: %h   in_acc: %h    MAC Unit Output: %h", test_inputs[i], test_weights[i], test_ps[i], mac_if.out_accumulate);
           #CLK_PERIOD;
           #CLK_PERIOD;
        end
        $finish;
    end

endmodule

