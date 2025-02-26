`timescale 1ns/1ps

`include "systolic_array_control_unit_if.vh"

module sysarr_control_unit_tb;

    // Parameters
    parameter PERIOD = 10;

    // Testbench Signals
    logic tb_tb_clk = 0;
    logic tb_nrst;


    // tb_clk init
    always #(PERIOD/2) tb_tb_clk++;
    // sysarr_control_unit_if instance
    systolic_array_control_unit_if cu_if();

    sysarr_control_unit dut (.tb_clk(tb_tb_clk), .nRST(tb_nrst), .cu(cu_if.control_unit));
    task reset;
        begin
        tb_nrst = 1'b0;
        @(posedge tb_tb_clk);
        @(posedge tb_tb_clk);
        @(negedge tb_tb_clk);
        tb_nrst = 1'b1;
        @(posedge tb_tb_clk);
        @(posedge tb_tb_clk);
        end
    endtask
    task wait_n_clocks(input int num_cycles);
        int i;
        for (i = 0; i < num_cycles; i = i + 1) begin
            @(posedge tb_clk); // Wait for one positive edge of clk
        end
    endtask
    // Test sequence
    initial begin
        // Initialize interface signals
        cu_if.weight_en = 0;
        cu_if.input_en = 0;
        cu_if.partial_en = 0;
        cu_if.row_en = 0;

        // Reset 
        reset();

        // Test Case 1: Load weights into the array
        cu_if.weight_en = 1;
        cu_if.row_en = 'd0; 
        @(posedge tb_clk); 
        cu_if.row_en = 'd1;
        @(posedge tb_clk); 
        cu_if.row_en = 'd2;
        @(posedge tb_clk); 
        cu_if.row_en = 'd3;
        @(posedge tb_clk);
        cu_if.weight_en = 0;

        // Test Case 2: Load inputs and partials into their fifos
        cu_if.input_en = 1;
        cu_if.partial_en = 1;
        cu_if.row_en = 'd0; //start_flag->next_iteration_full=1,nxt_mac_start=1
        @(posedge tb_clk); 
        cu_if.input_en = 0;
        cu_if.partial_en = 0;
        wait_n_clocks(5);
        cu_if.row_en = 'd1;
        wait_n_clocks(5); 
        cu_if.row_en = 'd2;
        wait_n_clocks(5); 
        cu_if.row_en = 'd3;
        wait_n_clocks(5);
        cu_if.input_en = 0;
        cu_if.partial_en = 0;


        // // Loading is complete
        // cu_if.row_en = 'b0000;
        // cu_if.input_en = 1;      // These two signals acitvate the start flag

        // Test Case 4: Check FIFO has space
        @(posedge tb_clk);
        $display("FIFO has space: %b", cu_if.fifo_has_space);

        // Test Case 5: Start MAC operations
        @(posedge tb_clk);
        $display("MAC start: %b, MAC count: %0d", cu_if.MAC_start, cu_if.MAC_count);

        // Test Case 6: Start addition operations
        @(posedge tb_clk);
        $display("Adder start: %b, Adder count: %0d", cu_if.add_start, cu_if.add_count);

        
        #100 
        $stop;
    end

endmodule
