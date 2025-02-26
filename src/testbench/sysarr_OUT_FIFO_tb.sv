`timescale 1ns / 1 ns

`include "systolic_array_OUT_FIFO_if.vh"

module sysarr_OUT_FIFO_tb();

// Parameters
parameter PERIOD = 10;

// Testbench Signals
logic tb_clk = 0;
logic tb_nrst;


// Clk init
always #(PERIOD/2) tb_clk++;
// FIFO_if instance
systolic_array_OUT_FIFO_if fifo_if();

sysarr_OUT_FIFO DUT (.nRST(tb_nrst), .clk(tb_clk), .fifo(fifo_if.OUT_FIFO));
task wait_n_clocks(input int num_cycles);
    int i;
    for (i = 0; i < num_cycles; i = i + 1) begin
        @(posedge tb_clk); // Wait for one positive edge of clk
    end
endtask
task reset;
    begin
      tb_nrst = 1'b0;
      @(posedge tb_clk);
      @(posedge tb_clk);
      @(negedge tb_clk);
      tb_nrst = 1'b1;
      @(posedge tb_clk);
      @(posedge tb_clk);
    end
endtask

// Test scenarios
initial begin
    // Initialize signals
    tb_clk = 0;
    tb_nrst = 0;
    fifo_if.shift = 0;
    fifo_if.shift_value = 0;

    // Reset 
    reset();
    // Test case 1: Shift values into the FIFO
    $display("fifo output before shift = %h", fifo_if.out);
    fifo_if.shift_value = 16'h0123; // Example data
    fifo_if.shift = 1; // Ensure data is only loaded when load signal is high
    wait_n_clocks(1);
    $display("fifo output after 1 shift = %h", fifo_if.out);
    fifo_if.shift_value = 16'h4567; // Example data
    fifo_if.shift = 1; // Ensure data is only loaded when load signal is high
    wait_n_clocks(1);
    $display("fifo output after 2 shift = %h", fifo_if.out);
    fifo_if.shift_value = 16'h89AB; // Example data
    fifo_if.shift = 1; // Ensure data is only loaded when load signal is high
    wait_n_clocks(1);
    $display("fifo output after 3 shift = %h", fifo_if.out);
    fifo_if.shift_value = 16'hCDEF; // Example data
    fifo_if.shift = 1; // Ensure data is only loaded when load signal is high
    wait_n_clocks(1);
    $display("fifo output after 4 shift = %h", fifo_if.out);
    fifo_if.shift = 0;
    //Test case 4: Checking reset
    reset();
    $display("fifo output after reset = %h", fifo_if.out);

    #50;
    $stop;
end

endmodule
