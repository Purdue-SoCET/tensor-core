`timescale 1ns / 1ps
`include "scheduler_buffer_if.vh"



module scheduler_buffer_tb();

// Parameters
localparam CLK_PERIOD = 10;

// Testbench Signals
logic CLK;
logic nRST;
scheduler_buffer_if scheduler_if();

// DUT instantiation
scheduler_buffer DUT (
    .CLK(CLK),
    .nRST(nRST),
    .mysche(scheduler_if)
);

// Clock Generation
always begin
    CLK = 1'b0;
    #(CLK_PERIOD/2.0);
    CLK = 1'b1;
    #(CLK_PERIOD/2.0);
end

// Task to add a request
task add_request(input logic [31:0] addr, input logic write, input logic [31:0] data);
    if (write) begin
        scheduler_if.dWEN = 1'b1;
        scheduler_if.dREN = 1'b0;
        scheduler_if.ramaddr = addr;
        scheduler_if.memstore = data;
    end else begin
        scheduler_if.dWEN = 1'b0;
        scheduler_if.dREN = 1'b1;
        scheduler_if.ramaddr = addr;
    end
    #(CLK_PERIOD);
    scheduler_if.dWEN = 1'b0;
    scheduler_if.dREN = 1'b0;
endtask

// Task to remove a request
task remove_request();
    scheduler_if.request_done = 1'b1;
    #(CLK_PERIOD);
    scheduler_if.request_done = 1'b0;
endtask

// Test Sequence
initial begin
    nRST = 1'b1;
    #(CLK_PERIOD*2);
    
    // Power-on Reset
    nRST = 1'b0;
    #(CLK_PERIOD*2);
    nRST = 1'b1;
    #(CLK_PERIOD*2);
    
    // Add requests
    add_request(32'hA000_0000, 1'b1, 32'hDEADBEEF);
    add_request(32'hB000_0000, 1'b0, 32'h0);
    #(CLK_PERIOD);
    
    // // Remove requests
    // remove_request();
    // remove_request();
    // #(CLK_PERIOD);
    
    $finish;
end

endmodule
