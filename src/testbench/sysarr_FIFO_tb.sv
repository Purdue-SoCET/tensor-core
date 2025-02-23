`timescale 1ns / 1 ns

`include "systolic_array_FIFO_if.vh"

module sysarr_FIFO_tb();

// Parameters
parameter PERIOD = 10;

// Testbench Signals
logic tb_clk = 0;
logic tb_nrst;


// Clk init
always #(PERIOD/2) tb_clk++;
// FIFO_if instance
systolic_array_FIFO_if fifo_if();

sysarr_FIFO DUT (.nRST(tb_nrst), .clk(tb_clk), .fifo(fifo_if.FIFO));
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
integer i;
// Test scenarios
initial begin
    // Initialize signals
    tb_clk = 0;
    tb_nrst = 0;
    fifo_if.load = 0;
    fifo_if.shift = 0;
    fifo_if.load_values = 0;

    // Reset 
    reset();
    // Test case 1: Load values into the FIFO
    $display("fifo output before load = %h", fifo_if.out);
    fifo_if.load_values = 64'h0123456789ABCDEF; // Example data
    fifo_if.load = 1; // Ensure data is only loaded when load signal is high
    @(posedge tb_clk);
    fifo_if.load = 0;
    $display("fifo output after load = %h", fifo_if.out);
    // Shift values out the FIFO
    for (i = 0; i <= 3; i = i + 1) begin
        fifo_if.shift = 1;
        @(posedge tb_clk);
        fifo_if.shift = 0; 
        $display("fifo_if.out = %h", fifo_if.out);
    end
    reset();
    // Test case 2: Load values into the FIFO while not done shifting out
    $display("fifo output before load = %h", fifo_if.out);
    fifo_if.load_values = 64'h0123456789ABCDEF; // Example data
    fifo_if.load = 1; // Ensure data is only loaded when load signal is high
    @(posedge tb_clk);
    fifo_if.load = 0;
    $display("fifo output after load = %h", fifo_if.out);
    //Shift values out the FIFO
    fifo_if.shift = 1;
    @(posedge tb_clk);
    fifo_if.shift = 0; 
    $display("fifo_if.out = %h", fifo_if.out);
    fifo_if.shift = 1;
    @(posedge tb_clk);
    fifo_if.shift = 0; 
    $display("fifo_if.out = %h", fifo_if.out);
    fifo_if.load_values = 64'h1212343456567878; // Example data
    fifo_if.load = 1; // Ensure data is only loaded when load signal is high
    @(posedge tb_clk);
    fifo_if.load = 0;
    for (i = 0; i <= 6; i = i + 1) begin
        fifo_if.shift = 1;
        @(posedge tb_clk);
        fifo_if.shift = 0; 
        $display("fifo_if.out = %h", fifo_if.out);
    end

    #50;
    $stop;
end

endmodule
